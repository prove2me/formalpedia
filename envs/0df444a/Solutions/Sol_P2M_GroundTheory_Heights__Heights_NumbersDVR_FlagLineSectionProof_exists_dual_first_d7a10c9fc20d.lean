-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_dual_first_d7a10c9fc20d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:44:46.706207+00:00
-- url     : https://prove2.me/submissions/1ef93911-148a-4d2b-a379-e48ebe52c11b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionSplit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_adapted_77e9c8dbc8e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartZ_ne_zero_c26e38d1d885
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_live_of_segreVec_ne_zero_8419d5c16931


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω] {F : Type*} [Field F]
  [Algebra F Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
theorem _root_.solution (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (h0 : 0 < N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing F (segreVec y) c) ∧
      ψ (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩) = 1 := by
  have hlive := live_of_segreVec_ne_zero hc
  choose e he hup hdiag using exists_adapted y B w b hB c hc
  have hm : ∀ i, chartZ y c (b i) ≠ 0 := fun i => chartZ_ne_zero hlive _
  have hspan : ∀ n : ℕ, ∀ i : Fin N, (i : ℕ) = n → w i ∈ Submodule.span Ω (Set.range e) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      have hsum := w.sum_repr (e i)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
      have hrest : ∑ j ∈ Finset.univ.erase i, w.repr (e i) j • w j ∈
          Submodule.span Ω (Set.range e) := by
        refine Submodule.sum_mem _ fun j hj => ?_
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hlt | hgt
        · exact Submodule.smul_mem _ _ (ih j (by rw [← hi]; exact hlt) j rfl)
        · rw [hup i j hgt, zero_smul]
          exact Submodule.zero_mem _
      have hei : e i ∈ Submodule.span Ω (Set.range e) := Submodule.subset_span ⟨i, rfl⟩
      have h1 : w.repr (e i) i • w i ∈ Submodule.span Ω (Set.range e) := by
        rw [eq_sub_of_add_eq hsum]
        exact Submodule.sub_mem _ hei hrest
      rw [hdiag] at h1
      have h2 := Submodule.smul_mem _ (chartZ y c (b i))⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ (hm i), one_smul] at h2
  have htop : ⊤ ≤ Submodule.span Ω (Set.range e) := by
    rw [← w.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hspan i i rfl
  have hcard : Fintype.card (Fin N) = Module.finrank Ω E := by
    rw [Module.finrank_eq_card_basis w]
  set eb := basisOfTopLeSpanOfCardEqFinrank e htop hcard with heb_def
  have heb : ∀ i, eb i = e i := fun i => by
    rw [heb_def, coe_basisOfTopLeSpanOfCardEqFinrank]
  set ψ : Module.Dual Ω E := eb.coord ⟨0, h0⟩ with hψ_def
  have hψe : ∀ i, ψ (e i) ∈ chartRing F (segreVec y) c := by
    intro i
    rw [← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hint : ∀ n : ℕ, n ≤ N → ∀ v ∈ B.lat c, (∀ j : Fin N, n ≤ (j : ℕ) → w.repr v j = 0) →
      ψ v ∈ chartRing F (segreVec y) c := by
    intro n
    induction n with
    | zero =>
      intro _ v _ hv
      have : v = 0 := w.repr.injective (by ext j; simp [hv j (Nat.zero_le _)])
      simp [this]
    | succ n ih =>
      intro hn v hvB hv
      set i : Fin N := ⟨n, hn⟩ with hi_def
      have hmem : w.repr v i ∈ degLat F y (b i) c := by
        rw [← hB.graded c hc i]
        refine ⟨v, hvB, fun j hj => hv j ?_, rfl⟩
        rw [Fin.lt_def] at hj
        simp only [hi_def] at hj
        omega
      obtain ⟨α, hα, hαv⟩ := hmem
      have hv' : v - α • e i ∈ B.lat c := (B.lat c).sub_mem hvB (B.stable c α hα _ (he i))
      have hrec := ih (by omega) _ hv' (fun j hj => by
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
        rcases Nat.lt_or_ge n (j : ℕ) with hlt | hge
        · rw [hv j (by omega), hup i j (by rw [Fin.lt_def]; exact hlt), mul_zero, sub_zero]
        · have hji : j = i := Fin.ext (by simp only [hi_def]; omega)
          rw [hji, hdiag, hαv]
          simp [chartZ])
      have hsplit : ψ v = ψ (v - α • e i) + α * ψ (e i) := by
        simp [map_sub, smul_eq_mul]
      rw [hsplit]
      exact add_mem hrec (mul_mem hα (hψe i))
  refine ⟨ψ, fun v hv => hint N le_rfl v hv (fun j hj => absurd j.isLt (by omega)), ?_⟩
  have he0 : e ⟨0, h0⟩ = chartZ y c (b ⟨0, h0⟩) • w ⟨0, h0⟩ := by
    conv_lhs => rw [← w.sum_repr (e ⟨0, h0⟩)]
    rw [Finset.sum_eq_single ⟨0, h0⟩]
    · rw [hdiag]
    · intro j _ hj
      rw [hup _ j (by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))), zero_smul]
    · simp
  have h1 : ψ (e ⟨0, h0⟩) = 1 := by
    rw [← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  rw [he0, map_smul, smul_eq_mul] at h1
  rw [mul_comm]
  exact h1
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
