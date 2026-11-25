-- Prove2me | solution 1 for UpperTheory.Mu.unitary_integral_finite_and_ncard_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:46:42.967069+00:00
-- url     : https://prove2.me/submissions/8feed66d-c3ba-4b49-a56a-1b19b5cc4833

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_Monomial
import Theorems.Thm_UpperTheory_Mu_exists_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open UpperTheory UpperTheory.Mu
variable {K : Type} [Field K] [NumberField K]
namespace UpperTheory.Mu
theorem _root_.solution [StarRing K]
    (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ) :
    {g : Matrix (Fin n) (Fin n) K | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.Finite ∧
    {g : Matrix (Fin n) (Fin n) K | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.ncard
      ≤ Units.torsionOrder K ^ n * n.factorial := by
  classical
  have hT : 0 < Units.torsionOrder K := Units.torsionOrder_pos K
  let R : Finset K := (Polynomial.nthRoots (Units.torsionOrder K) (1 : K)).toFinset
  let P : Finset ((Fin n → K) × Equiv.Perm (Fin n)) :=
    Fintype.piFinset (fun _ => R) ×ˢ Finset.univ
  let Φ : (Fin n → K) × Equiv.Perm (Fin n) → Matrix (Fin n) (Fin n) K :=
    fun p => Matrix.of fun a b => if a = p.2 b then p.1 b else 0
  have hsub : {g : Matrix (Fin n) (Fin n) K | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} ⊆
      ↑(P.image Φ) := by
    rintro g ⟨hg, hint⟩
    obtain ⟨t, σ, ht, rfl⟩ := exists_monomial hconj n g hg hint
    rw [Finset.coe_image]
    refine ⟨(t, σ), ?_, rfl⟩
    simp [P, R, Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset, Multiset.mem_toFinset,
      Polynomial.mem_nthRoots hT, ht]
  refine ⟨(P.image Φ).finite_toSet.subset hsub, ?_⟩
  calc _ ≤ (↑(P.image Φ) : Set (Matrix (Fin n) (Fin n) K)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (P.image Φ).card := Set.ncard_coe_finset _
    _ ≤ P.card := Finset.card_image_le
    _ = R.card ^ n * n.factorial := by
        simp [P, Fintype.card_piFinset, Fintype.card_perm]
    _ ≤ Units.torsionOrder K ^ n * n.factorial := by
        gcongr
        exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
end UpperTheory.Mu
