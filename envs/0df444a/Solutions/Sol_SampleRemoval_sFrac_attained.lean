-- Prove2me | solution 1 for SampleRemoval.sFrac_attained
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:34:45.484193+00:00
-- url     : https://prove2.me/submissions/2417c0e3-c2ef-4817-a8c1-2d5e879b72b2

import Mathlib
import Definitions.Def_SampleRemoval_feasible
import Definitions.Def_SampleRemoval_sFrac
import Definitions.Def_SampleRemoval_GeneralPosition
import Theorems.Thm_SampleRemoval_gram_posDef_iff_card_support

section
set_option autoImplicit false

open Matrix Filter Topology

namespace SampleRemoval.Dev.SFrac

lemma card_supp_of_mass {n d : ℕ} (w : Fin n → ℝ) (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1)
    (hm : (d : ℝ) - 1 < ∑ i, w i) : d ≤ (Finset.univ.filter (fun i => w i ≠ 0)).card := by
  have h1 : ∑ i, w i ≤ ((Finset.univ.filter (fun i => w i ≠ 0)).card : ℝ) := by
    rw [← Finset.sum_filter_ne_zero]
    calc ∑ i ∈ Finset.univ.filter (fun i => w i ≠ 0), w i
        ≤ ∑ i ∈ Finset.univ.filter (fun i => w i ≠ 0), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (hw i).2
      _ = _ := by simp
  have h2 : (d : ℝ) - 1 < ((Finset.univ.filter (fun i => w i ≠ 0)).card : ℝ) :=
    lt_of_lt_of_le hm h1
  have h3 : (d : ℝ) < ((Finset.univ.filter (fun i => w i ≠ 0)).card : ℝ) + 1 := by linarith
  have h4 : d < (Finset.univ.filter (fun i => w i ≠ 0)).card + 1 := by exact_mod_cast h3
  omega

lemma gram_cont {n d : ℕ} (x : Fin n → Fin d → ℝ) : Continuous (fun w : Fin n → ℝ => gram x w) := by
  unfold gram
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_apply i).smul continuous_const

lemma moment_cont {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) :
    Continuous (fun w : Fin n → ℝ => moment x y w) := by
  unfold moment
  refine continuous_finsetSum _ fun i _ => ?_
  exact (((continuous_apply i).mul continuous_const)).smul continuous_const

lemma ols_continuousAt {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w₀ : Fin n → ℝ)
    (hdet : (gram x w₀).det ≠ 0) : ContinuousAt (fun w => ols x y w) w₀ := by
  have hinv : ContinuousAt Inv.inv (gram x w₀) := by
    refine continuousAt_matrix_inv _ ?_
    have : (Ring.inverse : ℝ → ℝ) = Inv.inv := Ring.inverse_eq_inv'
    rw [this]; exact continuousAt_inv₀ hdet
  have h1 : ContinuousAt (fun w : Fin n → ℝ => (gram x w)⁻¹) w₀ :=
    ContinuousAt.comp (g := Inv.inv) (f := fun w : Fin n → ℝ => gram x w) hinv
      (gram_cont x).continuousAt
  have h2 : ContinuousAt (fun p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => p.1 *ᵥ p.2)
      ((gram x w₀)⁻¹, moment x y w₀) :=
    (continuous_fst.matrix_mulVec continuous_snd).continuousAt
  exact ContinuousAt.comp (g := fun p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => p.1 *ᵥ p.2)
    (f := fun w => ((gram x w)⁻¹, moment x y w)) h2 (h1.prodMk (moment_cont x y).continuousAt)

end SampleRemoval.Dev.SFrac

namespace SampleRemoval

open Matrix

theorem chk_sFrac_attained {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ)
    (θ : ℝ) (hGP : GeneralPosition x) (hne : (feasible x y e θ).Nonempty)
    (h : (d : ℝ) - 1 < n - sFrac x y e θ) :
    ∃ w ∈ feasible x y e θ, (n : ℝ) - ∑ i, w i = sFrac x y e θ := by
  set s := sFrac x y e θ with hs
  have hne' : ((fun w : Fin n → ℝ => (n : ℝ) - ∑ i, w i) '' feasible x y e θ).Nonempty :=
    hne.image _
  have hbdd : BddBelow ((fun w : Fin n → ℝ => (n : ℝ) - ∑ i, w i) '' feasible x y e θ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have : ∑ i, w i ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hw.1 i).2
    simp at this
    linarith
  have hex : ∀ k : ℕ, ∃ w ∈ feasible x y e θ, (n : ℝ) - ∑ i, w i < s + 1 / ((k : ℝ) + 1) := by
    intro k
    have : s < s + 1 / ((k : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne' this
    exact ⟨w, hw, hlt⟩
  choose f hfW hfs using hex
  have hlow : ∀ k, s ≤ (n : ℝ) - ∑ i, f k i :=
    fun k => csInf_le hbdd ⟨f k, hfW k, rfl⟩
  have hcomp : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hcomp.tendsto_subseq
    (x := f) (fun k => Set.mem_univ_pi.mpr (hfW k).1)
  have haI : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1 := Set.mem_univ_pi.mp ha
  -- mass
  have hmass_cont : Continuous (fun w : Fin n → ℝ => (n : ℝ) - ∑ i, w i) := by fun_prop
  have hT1 : Tendsto (fun k => (n : ℝ) - ∑ i, f (φ k) i) atTop (𝓝 ((n : ℝ) - ∑ i, a i)) :=
    (hmass_cont.tendsto a).comp hlim
  have hT2 : Tendsto (fun k => (n : ℝ) - ∑ i, f (φ k) i) atTop (𝓝 s) := by
    have hup : Tendsto (fun k => s + 1 / ((φ k : ℝ) + 1)) atTop (𝓝 s) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      simpa using (tendsto_const_nhds (x := s)).add this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => hlow (φ k)) (fun k => (hfs (φ k)).le)
  have hmass : (n : ℝ) - ∑ i, a i = s := tendsto_nhds_unique hT1 hT2
  have hm : (d : ℝ) - 1 < ∑ i, a i := by linarith
  have hPD : (gram x a).PosDef :=
    (SampleRemoval.gram_posDef_iff_card_support x hGP a haI).mpr
      (Dev.SFrac.card_supp_of_mass a haI hm)
  have hdet : (gram x a).det ≠ 0 := hPD.det_pos.ne'
  have hcont := Dev.SFrac.ols_continuousAt x y a hdet
  have hdot : Continuous (fun b : Fin d → ℝ => e ⬝ᵥ b) := by
    unfold dotProduct; fun_prop
  have hT3 : Tendsto (fun k => e ⬝ᵥ ols x y (f (φ k))) atTop (𝓝 (e ⬝ᵥ ols x y a)) :=
    (hdot.tendsto _).comp (hcont.tendsto.comp hlim)
  have hle : e ⬝ᵥ ols x y a ≤ θ :=
    le_of_tendsto hT3 (Eventually.of_forall fun k => (hfW (φ k)).2.2)
  exact ⟨a, ⟨haI, hPD, hle⟩, hmass⟩

end SampleRemoval
end

theorem solution : type_of% @SampleRemoval.chk_sFrac_attained := @SampleRemoval.chk_sFrac_attained
