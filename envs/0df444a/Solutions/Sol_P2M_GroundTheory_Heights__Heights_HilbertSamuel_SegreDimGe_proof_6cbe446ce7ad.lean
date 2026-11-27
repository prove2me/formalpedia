-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SegreDimGe_proof_6cbe446ce7ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:58:02.176479+00:00
-- url     : https://prove2.me/submissions/bbcd68a9-4c05-47a6-8386-9075da192e79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreDimGe
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSegreDimGe
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_exists_ringKrullDim_eq_trdeg
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_X_c51f5f5b34ef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Cardinal
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace SegreDimGe
theorem _root_.solution : SegreDimGe.Statement := by
  intro F _ K _ _ _ ι _ q e hq hdim
  have := hq.isPrime
  let π : MRing ι F →ₐ[F] MRing ι F ⧸ q := Ideal.Quotient.mkₐ F q
  let φ : MRing (fun _ : Unit => ∀ k, ι k) F →ₐ[F] MRing ι F ⧸ q := π.comp (segreMap F)
  let R' : Subalgebra F (MRing ι F ⧸ q) := φ.range
  choose i hi using hq.relevant
  let x : K → MRing ι F ⧸ q := fun k => π (X ⟨k, i k⟩)
  have hx0 : ∀ k, x k ≠ 0 := fun k h =>
    hi k (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [x, π, Ideal.Quotient.mkₐ_eq_mk] using h))

  have hkey : ∀ k (j : ι k), (∏ l ∈ Finset.univ.erase k, x l) * π (X ⟨k, j⟩) =
      φ (X ⟨(), Function.update i k j⟩) := by
    intro k j
    rw [AlgHom.comp_apply, segreMap_X, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  let k0 : K := Classical.arbitrary K
  let s : Set (MRing ι F ⧸ q) := x '' ↑(Finset.univ.erase k0)
  let B : Subalgebra R' (MRing ι F ⧸ q) := Algebra.adjoin R' s
  have hR'B : ∀ a ∈ R', IsAlgebraic B a := fun a ha =>
    isAlgebraic_algebraMap (⟨a, Subalgebra.algebraMap_mem B (⟨a, ha⟩ : R')⟩ : B)
  have hsB : ∀ l, l ≠ k0 → IsAlgebraic B (x l) := fun l hl =>
    isAlgebraic_algebraMap (⟨x l, Algebra.subset_adjoin
      ⟨l, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩), rfl⟩⟩ : B)
  have hgen : ∀ k, (∀ l, l ≠ k → IsAlgebraic B (x l)) → ∀ j : ι k, IsAlgebraic B (π (X ⟨k, j⟩)) := by
    intro k hk j
    have hy : IsAlgebraic B (∏ l ∈ Finset.univ.erase k, x l) :=
      Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isAlgebraic_one
        fun l hl => hk l (Finset.ne_of_mem_erase hl)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero ?_) hy ?_
    · exact Finset.prod_ne_zero_iff.mpr fun l _ => hx0 l
    · rw [hkey]
      exact hR'B _ ⟨_, rfl⟩
  have hall : ∀ l, IsAlgebraic B (x l) := by
    intro l
    by_cases hl : l = k0
    · subst hl
      exact hgen _ hsB (i _)
    · exact hsB l hl
  have hA : ∀ a : MRing ι F ⧸ q, IsAlgebraic B a := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective F q a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.algHom_C]
      exact hR'B _ (R'.algebraMap_mem c)
    | add p r hp hr => rw [map_add]; exact hp.add hr
    | mul_X p v hp => rw [map_mul]; exact hp.mul (hgen v.1 (fun l _ => hall l) v.2)
  have : Algebra.IsAlgebraic B (MRing ι F ⧸ q) := ⟨hA⟩
  have htop : Algebra.trdeg R' (MRing ι F ⧸ q) ≤ #s := Algebra.IsAlgebraic.trdeg_le_cardinalMk R' s
  have hs : #s ≤ (Fintype.card K - 1 : ℕ) := by
    refine Cardinal.mk_image_le.trans ?_
    simp
  have : FaithfulSMul F R' :=
    (faithfulSMul_iff_algebraMap_injective F R').mpr (algebraMap F R').injective
  have : FaithfulSMul R' (MRing ι F ⧸ q) :=
    ⟨fun {r₁ r₂} h => Subtype.ext (by simpa [Subalgebra.smul_def] using h 1)⟩
  have htower := trdeg_add_eq (A := MRing ι F ⧸ q) F R'

  let g : (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q) →ₐ[F] R' :=
    Ideal.Quotient.liftₐ (segrePrime F q) φ.rangeRestrict fun p hp => by
      apply Subtype.ext
      simpa [φ, π, segrePrime, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hp
  have hg : Function.Surjective g := by
    rintro ⟨y, p, rfl⟩
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have hR'le := trdeg_le_of_surjective g hg
  obtain ⟨n, hn, htn⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := F) (A := MRing ι F ⧸ q)
  obtain ⟨m, hm, htm⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := F) (A := MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q)
  have hne : n = e + Fintype.card K := by
    rw [hn] at hdim
    exact_mod_cast hdim
  have hcard : (n : Cardinal) ≤ (m + (Fintype.card K - 1) : ℕ) := by
    rw [← htn, ← htower, Nat.cast_add, ← htm]
    exact add_le_add hR'le (htop.trans hs)
  have hK : 0 < Fintype.card K := Fintype.card_pos
  have hnm : n ≤ m + (Fintype.card K - 1) := by exact_mod_cast hcard
  rw [hm]
  exact_mod_cast (show e + 1 ≤ m by omega)
end SegreDimGe
end GroundTheory.Heights₂.Heights.HilbertSamuel
