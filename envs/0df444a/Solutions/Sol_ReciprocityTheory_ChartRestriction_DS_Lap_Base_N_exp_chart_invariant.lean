-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exp_chart_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:44.657779+00:00
-- url     : https://prove2.me/submissions/af9a39b3-2e53-4ad9-b4e5-ba2c546834fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_shear_preserving
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_iter_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_iter_differentiable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_shear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_mem_lieN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_neg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_mem_grpN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_injOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_lg_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_mul_mem_grpN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}
variable [FiniteDimensional ℝ A]
variable {st : A →ₗ[ℝ] A}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (hF : IsFil F L) (hst : IsAdj F st)
    [MeasurableSpace (lieN F st)] [BorelSpace (lieN F st)] (μ : Measure (lieN F st))
    [μ.IsAddHaarMeasure] {s : A} (hs : s ∈ grpN F st) :
    ∃ Φ : lieN F st → lieN F st, MeasurePreserving Φ μ μ ∧
      ∀ Y, NormedSpace.exp (Φ Y : A) = s * NormedSpace.exp (Y : A) := by
  have hE := hF.exp_shear
  have hY0 : ∀ Y : lieN F st, (Y : A) ∈ F 0 := fun Y => (mem_lieN.1 Y.2).1
  have hmem : ∀ Y : lieN F st, s * NormedSpace.exp (Y : A) ∈ grpN F st :=
    fun Y => mul_mem_grpN hF hst hs (exp_mem_grpN hF hst Y.2)
  let Φ : lieN F st → lieN F st := fun Y =>
    ⟨lg L (s * NormedSpace.exp (Y : A)), (lg_spec hF hst (hmem Y)).1⟩
  have hΦ : ∀ Y, NormedSpace.exp (Φ Y : A) = s * NormedSpace.exp (Y : A) :=
    fun Y => (lg_spec hF hst (hmem Y)).2
  refine ⟨Φ, ?_, hΦ⟩
  have hs' := hs
  obtain ⟨hs1, hs2⟩ := hs'
  have hmulS : IsShear F (fun u => s * (u + 1) - 1) := by
    refine ⟨fun u hu => ?_, fun j u hu v hv huv => ?_⟩
    · show s * (u + 1) - 1 ∈ F 0
      have e : s * (u + 1) - 1 = (s - 1) * u + u + (s - 1) := by noncomm_ring
      rw [e]
      exact (F 0).add_mem ((F 0).add_mem
        (hF.anti 0 (0 + 0 + 1) (Nat.zero_le _) (hF.mul 0 0 _ _ hs1 hu)) hu) hs1
    · show s * (u + 1) - 1 - (s * (v + 1) - 1) - (u - v) ∈ F (j + 1)
      have e : s * (u + 1) - 1 - (s * (v + 1) - 1) - (u - v) = (s - 1) * (u - v) := by
        noncomm_ring
      rw [e]
      have h := hF.mul 0 j _ _ hs1 huv
      rwa [Nat.zero_add] at h
  have hT := IsShear.comp hF (IsShear.inv hF hE) (IsShear.comp hF hmulS hE)
  have hΦT : ∀ Y : lieN F st, (Φ Y : A) = (iter (fun x => NormedSpace.exp x - 1) L ∘
      ((fun u => s * (u + 1) - 1) ∘ (fun x => NormedSpace.exp x - 1))) (Y : A) := by
    intro Y
    show lg L (s * NormedSpace.exp (Y : A)) =
      iter (fun x => NormedSpace.exp x - 1) L (s * (NormedSpace.exp (Y : A) - 1 + 1) - 1)
    rw [sub_add_cancel]
    rfl
  let E' : A → A := fun x => x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)
  have hEE' : ∀ x ∈ F 0, E' x = NormedSpace.exp x - 1 := by
    intro x hx
    show x + _ = _
    rw [hF.exp_eq hx]
    abel
  have hpw : ∀ m : ℕ, Differentiable ℝ (fun x : A => x ^ m) := by
    intro m
    induction m with
    | zero => simp only [pow_zero]; exact differentiable_const _
    | succ m ih => simp only [pow_succ]; exact ih.mul differentiable_id
  have hsd : Differentiable ℝ
      (fun x : A => ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)) := by
    have h : Differentiable ℝ
        (∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • fun x : A => x ^ (k + 2)) :=
      Differentiable.sum fun k _ => (hpw (k + 2)).const_smul _
    rw [Finset.sum_fn] at h
    exact h
  have hE'd : Differentiable ℝ E' := differentiable_id.add hsd
  have hiter : ∀ z ∈ F 0, ∀ i, iter E' i z = iter (fun x => NormedSpace.exp x - 1) i z := by
    intro z hz i
    induction i with
    | zero => rfl
    | succ i ih =>
      show iter E' i z + (z - E' (iter E' i z)) = iter (fun x => NormedSpace.exp x - 1) i z +
        (z - (NormedSpace.exp (iter (fun x => NormedSpace.exp x - 1) i z) - 1))
      rw [ih, hEE' _ (IsShear.iter_mem hE hz i).1]
  have hgΦ : ∀ Y : lieN F st, (Φ Y : A) = iter E' L (s * (E' (Y : A) + 1) - 1) := by
    intro Y
    rw [hΦT Y, hEE' _ (hY0 Y)]
    have hz : s * (NormedSpace.exp (Y : A) - 1 + 1) - 1 ∈ F 0 := hmulS.1 _ (hE.1 _ (hY0 Y))
    exact (hiter _ hz L).symm
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (lieN F st)
  let π : A →L[ℝ] lieN F st :=
    LinearMap.toContinuousLinearMap (Submodule.linearProjOfIsCompl (lieN F st) q hq)
  have hπ : ∀ Y : lieN F st, π (Y : A) = Y := fun Y =>
    Submodule.linearProjOfIsCompl_apply_left hq Y
  have hΦd : Differentiable ℝ Φ := by
    have e : Φ = fun Y : lieN F st => π (iter E' L (s * (E' (Y : A) + 1) - 1)) := by
      funext Y
      rw [← hgΦ Y, hπ]
    rw [e]
    have hsub : Differentiable ℝ (fun Y : lieN F st => (Y : A)) :=
      (lieN F st).subtypeL.differentiable
    exact π.differentiable.comp ((iter_differentiable hE'd L).comp
      ((((hE'd.comp hsub).add_const 1).const_mul s).sub_const 1))
  refine shear_preserving μ (fun j => (F j).comap (lieN F st).subtype) L ?_ ?_ Φ hΦd ?_ ?_
  · rw [eq_top_iff]
    intro Y _
    exact hY0 Y
  · rw [eq_bot_iff]
    intro Y hY
    have h : (Y : A) ∈ F L := hY
    rw [hF.bot, Submodule.mem_bot] at h
    rw [Submodule.mem_bot]
    exact Subtype.ext h
  · refine ⟨fun Y Y' h => ?_, fun Z => ?_⟩
    · have h2 : s * NormedSpace.exp (Y : A) = s * NormedSpace.exp (Y' : A) := by
        rw [← hΦ Y, ← hΦ Y', h]
      have h3 : NormedSpace.exp (Y : A) = NormedSpace.exp (Y' : A) := by
        calc NormedSpace.exp (Y : A) = st s * s * NormedSpace.exp (Y : A) := by rw [hs2, one_mul]
          _ = st s * (s * NormedSpace.exp (Y' : A)) := by rw [mul_assoc, h2]
          _ = NormedSpace.exp (Y' : A) := by rw [← mul_assoc, hs2, one_mul]
      exact Subtype.ext (exp_injOn hF (hY0 Y) (hY0 Y') h3)
    · obtain ⟨hls, hexps⟩ := lg_spec hF hst hs
      have hsinv : s * NormedSpace.exp (-(lg L s)) = 1 := by
        have h4 := (exp_neg_mul (lg L s)).2
        rwa [hexps] at h4
      have hm := mul_mem_grpN hF hst (exp_mem_grpN hF hst ((lieN F st).neg_mem hls))
        (exp_mem_grpN hF hst Z.2)
      refine ⟨⟨lg L (NormedSpace.exp (-(lg L s)) * NormedSpace.exp (Z : A)),
        (lg_spec hF hst hm).1⟩, ?_⟩
      apply Subtype.ext
      apply exp_injOn hF (hY0 _) (hY0 Z)
      rw [hΦ]
      show s * NormedSpace.exp (lg L (NormedSpace.exp (-(lg L s)) * NormedSpace.exp (Z : A))) = _
      rw [(lg_spec hF hst hm).2, ← mul_assoc, hsinv, one_mul]
  · intro j x y hxy
    have hxy' : (x : A) - (y : A) ∈ F j := hxy
    show (Φ x : A) - (Φ y : A) - ((x : A) - (y : A)) ∈ F (j + 1)
    rw [hΦT x, hΦT y]
    exact hT.2 j _ (hY0 x) _ (hY0 y) hxy'
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
