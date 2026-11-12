-- Prove2me | solution 1 for ProcessingNetworks.EntropyIneq.lemma_B_14
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:47:06.187335+00:00
-- url     : https://prove2.me/submissions/fc62da45-a8be-4672-9055-506dc896d50e

import Mathlib
import Definitions.Def_RobustToDynamics_specRadius
import Definitions.Def_ProcessingNetworks_EntropyIneq_outflow
import Theorems.Thm_ProcessingNetworks_EntropyIneq_theorem_F_1

open Matrix ProcessingNetworks.EntropyIneq

theorem solution {I : ℕ} (hI : 0 < I) (P : Matrix (Fin I) (Fin I) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hρ : RobustToDynamics.specRadius P < 1)
    (α : Fin I → ℝ) (hα : ∀ i, 0 < α i) (δ : ℝ) (hδ : 0 < δ) :
    ∃ κ : ℝ,
      IsLeast ((fun d : Fin I → ℝ => ∑ i, α i * |d i - (∑ j, P i j * d j + outflow P i)|) ''
          {d : Fin I → ℝ | (∀ i, 0 ≤ d i) ∧ δ ≤ ∑ i, |d i - 1|}) κ ∧
        0 < κ := by
  let _ := hP
  have hTFAE2 : IsUnit (1 - P) ∧
      Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, P ^ k) Filter.atTop (nhds (1 - P)⁻¹) :=
    ((theorem_F_1 P).out 1 2).mp hρ
  have hu : IsUnit (1 - P) := hTFAE2.1
  have hdet : IsUnit (1 - P).det := (Matrix.isUnit_iff_isUnit_det (1 - P)).mp hu
  let B : Matrix (Fin I) (Fin I) ℝ := (1 - P)⁻¹
  have hB_left : B * (1 - P) = 1 := Matrix.nonsing_inv_mul (1 - P) hdet
  let f : (Fin I → ℝ) → ℝ :=
    fun d => ∑ i, α i * |d i - (∑ j, P i j * d j + outflow P i)|
  let S : Set (Fin I → ℝ) := {d : Fin I → ℝ | (∀ i, 0 ≤ d i) ∧ δ ≤ ∑ i, |d i - 1|}
  let e : Fin I → ℝ := fun _ => 1
  have hres : ∀ (d : Fin I → ℝ) (i : Fin I),
      d i - (∑ j, P i j * d j + outflow P i) = ((1 - P) *ᵥ (d - e)) i := by
    intro d i
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, outflow, e, mul_sub, mul_one,
      Finset.sum_sub_distrib]
    ring
  let M : ℝ := 1 + ∑ k : Fin I, ∑ i : Fin I, |B k i| / α i
  have hM_pos : 0 < M := by
    have : 0 ≤ ∑ k : Fin I, ∑ i : Fin I, |B k i| / α i :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ =>
        div_nonneg (abs_nonneg _) (hα i).le
    dsimp [M]
    linarith
  have hcoerc : ∀ d : Fin I → ℝ, ∑ k, |d k - 1| ≤ M * f d := by
    intro d
    let w : Fin I → ℝ := (1 - P) *ᵥ (d - e)
    have hde : d - e = B *ᵥ w := by
      dsimp [w]
      rw [Matrix.mulVec_mulVec, hB_left, Matrix.one_mulVec]
    have hpt_k : ∀ k : Fin I, |d k - 1| ≤ ∑ i, |B k i| * |w i| := by
      intro k
      have hk : d k - 1 = (d - e) k := rfl
      rw [hk, hde]
      simp only [Matrix.mulVec, dotProduct]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => le_of_eq (abs_mul (B k i) (w i)))
    have hsum1 : ∑ k, |d k - 1| ≤ ∑ i, (∑ k, |B k i|) * |w i| := by
      calc ∑ k, |d k - 1|
          ≤ ∑ k, ∑ i, |B k i| * |w i| := Finset.sum_le_sum fun k _ => hpt_k k
        _ = ∑ i, ∑ k, |B k i| * |w i| := Finset.sum_comm
        _ = ∑ i, (∑ k, |B k i|) * |w i| :=
            Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    have hcol_le : ∀ i : Fin I, ∑ k, |B k i| ≤ M * α i := by
      intro i
      have h1 : (∑ k, |B k i|) / α i ≤ ∑ k, ∑ j, |B k j| / α j := by
        rw [Finset.sum_div]
        exact Finset.sum_le_sum fun k _ =>
          Finset.single_le_sum (fun j _ => div_nonneg (abs_nonneg _) (hα j).le)
            (Finset.mem_univ i)
      have h2 : (∑ k, |B k i|) / α i ≤ M := by dsimp [M]; linarith
      exact (div_le_iff₀ (hα i)).mp h2
    have hfw : f d = ∑ i, α i * |w i| := by
      dsimp [f, w]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hres d i]
    calc ∑ k, |d k - 1|
        ≤ ∑ i, (∑ k, |B k i|) * |w i| := hsum1
      _ ≤ ∑ i, (M * α i) * |w i| :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcol_le i) (abs_nonneg _)
      _ = M * ∑ i, α i * |w i| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => mul_assoc M (α i) |w i|
      _ = M * f d := by rw [hfw]
  let d0 : Fin I → ℝ := fun _ => 1 + δ
  have hd0_S : d0 ∈ S := by
    refine ⟨fun _ => by dsimp [d0]; linarith, ?_⟩
    have hcard : (1 : ℝ) ≤ (I : ℝ) := Nat.one_le_cast.mpr hI
    have hsum_d0 : ∑ _ : Fin I, |(1 + δ) - 1| = (I : ℝ) * δ := by
      simp [abs_of_pos hδ]
    dsimp [d0]
    rw [hsum_d0]
    nlinarith
  let U : ℝ := 1 + M * f d0
  let K : Set (Fin I → ℝ) :=
    {d : Fin I → ℝ | (∀ i, 0 ≤ d i) ∧ (∀ i, d i ≤ U) ∧ δ ≤ ∑ i, |d i - 1|}
  have hd0_K : d0 ∈ K := by
    refine ⟨hd0_S.1, fun i => ?_, hd0_S.2⟩
    have hsingle : |d0 i - 1| ≤ ∑ k, |d0 k - 1| :=
      Finset.single_le_sum (f := fun k : Fin I => |d0 k - 1|)
        (fun k _ => abs_nonneg (d0 k - 1)) (Finset.mem_univ i)
    have hleM : δ ≤ M * f d0 := by
      have : |d0 i - 1| = δ := by dsimp [d0]; simp [abs_of_pos hδ]
      linarith [hcoerc d0]
    dsimp [d0, U]
    linarith
  have hK_closed : IsClosed K := by
    have hc1 : IsClosed {d : Fin I → ℝ | ∀ i, 0 ≤ d i} := by
      have heq : {d : Fin I → ℝ | ∀ i, 0 ≤ d i} = ⋂ i : Fin I, {d : Fin I → ℝ | 0 ≤ d i} := by
        ext d; simp
      rw [heq]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have hc2 : IsClosed {d : Fin I → ℝ | ∀ i, d i ≤ U} := by
      have heq : {d : Fin I → ℝ | ∀ i, d i ≤ U} = ⋂ i : Fin I, {d : Fin I → ℝ | d i ≤ U} := by
        ext d; simp
      rw [heq]
      exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
    have hc3 : IsClosed {d : Fin I → ℝ | δ ≤ ∑ i, |d i - 1|} :=
      isClosed_le continuous_const
        (continuous_finsetSum _ fun i _ => ((continuous_apply i).sub continuous_const).abs)
    exact hc1.inter (hc2.inter hc3)
  have hbox_compact : IsCompact (Set.pi Set.univ fun _ : Fin I => Set.Icc (0 : ℝ) U) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hK_compact : IsCompact K := by
    refine hbox_compact.of_isClosed_subset hK_closed ?_
    intro d hd i _
    exact ⟨hd.1 i, hd.2.1 i⟩
  have hf_cont : Continuous f := by
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    exact ((continuous_apply i).sub
      ((continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)).add
        continuous_const)).abs
  obtain ⟨dStar, hdStar_K, hdStar_min⟩ :=
    hK_compact.exists_isMinOn ⟨d0, hd0_K⟩ hf_cont.continuousOn
  have hdStar_S : dStar ∈ S := ⟨hdStar_K.1, hdStar_K.2.2⟩
  refine ⟨f dStar, ⟨⟨dStar, hdStar_S, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨d, hdS, rfl⟩
    by_cases hU : ∀ i, d i ≤ U
    · exact hdStar_min ⟨hdS.1, hU, hdS.2⟩
    · push Not at hU
      obtain ⟨i₀, hi₀⟩ := hU
      have hi₀_abs : M * f d0 < |d i₀ - 1| := by
        have h1 : M * f d0 < d i₀ - 1 := by dsimp [U] at hi₀; linarith
        exact h1.trans_le (le_abs_self _)
      have hsingle : |d i₀ - 1| ≤ ∑ k, |d k - 1| :=
        Finset.single_le_sum (f := fun k : Fin I => |d k - 1|)
          (fun k _ => abs_nonneg (d k - 1)) (Finset.mem_univ i₀)
      have hltM : M * f d0 < M * f d := (hi₀_abs.trans_le hsingle).trans_le (hcoerc d)
      have hfd0_lt : f d0 < f d := lt_of_mul_lt_mul_left hltM hM_pos.le
      exact (hdStar_min hd0_K).trans hfd0_lt.le
  · have hδ_le : δ ≤ M * f dStar := hdStar_S.2.trans (hcoerc dStar)
    have hpos_div : 0 < δ / M := div_pos hδ hM_pos
    exact hpos_div.trans_le ((div_le_iff₀ hM_pos).mpr (by linarith))
