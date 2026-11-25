-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.isUnit_mk_chartIdeal_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:44.230138+00:00
-- url     : https://prove2.me/submissions/60f7ea1e-d3d3-4e1d-9148-8bb354c6d0ba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_dim_add_one_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mk_chartIdeal_X_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) (j : ∀ k, ι k)
    (p : Σ k, ι k) (hp : (X p : MRingOver F ι) ∉ V) :
    IsUnit (Ideal.Quotient.mk (chartIdeal V j) (X p)) := by
  classical
  by_contra hu
  obtain ⟨M, hM, hpM⟩ := exists_max_ideal_of_mem_nonunits hu
  have hVp : V.IsPrime := hV.1.1
  letI : Field (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) := Ideal.Quotient.field M
  let θ : MRingOver F ι →ₐ[F] MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
    (IsScalarTower.toAlgHom F (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) (MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)))).comp
      ((Ideal.Quotient.mkₐ F M).comp (Ideal.Quotient.mkₐ F (chartIdeal V j)))
  have hθ : ∀ g, θ g = MvPolynomial.C (Ideal.Quotient.mk M (Ideal.Quotient.mk (chartIdeal V j) g)) := fun g => rfl
  let c : Finset K → K → MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
    fun S k => if k ∈ S then 0 else MvPolynomial.X k
  let φ : Finset K → MRingOver F ι →ₐ[F] MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
    fun S => aeval fun q => c S q.1 * θ (X q)
  have hφX : ∀ S q, φ S (X q) = c S q.1 * θ (X q) := fun S q => aeval_X _ _
  let Q : Finset K → Ideal (MRingOver F ι) := fun S => RingHom.ker (φ S)
  have hQp : ∀ S, (Q S).IsPrime := fun S => RingHom.ker_isPrime (φ S).toRingHom
  have hVQ : ∀ S, V ≤ Q S := fun S g hg => RingHom.mem_ker.mpr
    (aeval_blockScale_eq_zero hV.1.2.1 (c S) θ (fun g hg => by
      rw [hθ, Ideal.Quotient.eq_zero_iff_mem.mpr (show g ∈ chartIdeal V j from Ideal.mem_sup_left hg),
        map_zero, map_zero]) hg)

  have hmono : ∀ S k, Q S ≤ Q (insert k S) := by
    intro S k g hg
    let ρ : MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) →ₐ[F] MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
      (aeval fun k' => if k' = k then 0 else MvPolynomial.X k').restrictScalars F
    have e : ρ.comp (φ S) = φ (insert k S) := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rw [AlgHom.comp_apply, hφX, hφX, map_mul]
      congr 1
      · by_cases h1 : q.1 ∈ S
        · simp [ρ, c, h1]
        · by_cases h2 : q.1 = k
          · subst h2
            simp [ρ, c, h1]
          · simp [ρ, c, h1, h2]
      · rw [hθ]
        simp [ρ, MvPolynomial.algebraMap_eq]
    have hg' : φ S g = 0 := RingHom.mem_ker.mp hg
    show φ (insert k S) g = 0
    rw [← e, AlgHom.comp_apply, hg', map_zero]
  have hin : ∀ S k, (X ⟨k, j k⟩ : MRingOver F ι) ∈ Q (insert k S) := by
    intro S k
    show φ (insert k S) (X ⟨k, j k⟩) = 0
    rw [hφX]
    simp [c]
  have hout : ∀ S k, k ∉ S → (X ⟨k, j k⟩ : MRingOver F ι) ∉ Q S := by
    intro S k hk h
    have h' : φ S (X ⟨k, j k⟩) = 0 := RingHom.mem_ker.mp h
    rw [hφX, hθ, mk_chartIdeal_X_self, map_one, map_one, mul_one] at h'
    simp only [c, if_neg hk] at h'
    exact MvPolynomial.X_ne_zero k h'
  have hbase : (X p : MRingOver F ι) ∈ Q ∅ := by
    show φ ∅ (X p) = 0
    rw [hφX, hθ, Ideal.Quotient.eq_zero_iff_mem.mpr hpM, map_zero, mul_zero]
  have chain : ∀ S : Finset K, ((S.card : ℕ) : WithBot ℕ∞) + 1 + ringKrullDim (MRingOver F ι ⧸ Q S) ≤
      ringKrullDim (MRingOver F ι ⧸ V) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have := cyc_dim_add_one_le (hVQ ∅) hbase hp
      rw [Finset.card_empty, Nat.cast_zero, zero_add, add_comm]
      exact this
    | @insert k S hk ih =>
      have : (Q S).IsPrime := hQp S
      have h1 := cyc_dim_add_one_le (hmono S k) (hin S k) (hout S k hk)
      rw [Finset.card_insert_of_notMem hk]
      calc (((S.card + 1 : ℕ)) : WithBot ℕ∞) + 1 + ringKrullDim (MRingOver F ι ⧸ Q (insert k S))
          = (S.card : WithBot ℕ∞) + 1 + (ringKrullDim (MRingOver F ι ⧸ Q (insert k S)) + 1) := by
            push_cast; abel
        _ ≤ (S.card : WithBot ℕ∞) + 1 + ringKrullDim (MRingOver F ι ⧸ Q S) := add_le_add_right h1 _
        _ ≤ _ := ih
  have h := chain Finset.univ
  have : (Q Finset.univ).IsPrime := hQp _
  have : IsDomain (MRingOver F ι ⧸ Q Finset.univ) := Ideal.Quotient.isDomain _
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRingOver F ι ⧸ Q Finset.univ) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [hV.2, Finset.card_univ] at h
  have h2 : (((Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) ≤ ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    calc (((Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) = (Fintype.card K : WithBot ℕ∞) + 1 + 0 := by
          push_cast; simp
      _ ≤ _ := add_le_add_right h0 _
      _ ≤ _ := h
  have h3 : Fintype.card K + 1 ≤ 0 + Fintype.card K := by exact_mod_cast h2
  omega
end ReciprocityTheory.ChartRestriction.G.AI.I1
