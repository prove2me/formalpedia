-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoin_ringKrullDim_quotient_ker_39672f46aed5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:51:24.183595+00:00
-- url     : https://prove2.me/submissions/e69441c3-92b2-4eb6-884e-ce7246eb50d9

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_C_int_cc39e8a8b312
import Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TrdegAdjoin
open MvPolynomial Algebra Cardinal
attribute [local instance] MvPolynomial.algebraMvPolynomial
noncomputable section
variable {σ : Type} [Fintype σ] {L : Type} [CommRing L] [IsDomain L] [Algebra ℚ L]
namespace GroundTheory.Heights₂.Heights.TrdegAdjoin
theorem _root_.solution (φ : MvPolynomial σ ℤ →+* L) :
    ∃ s : ℕ, Algebra.trdeg ℚ (adjoin ℚ (Set.range fun v ↦ φ (X v))) = s ∧
      ringKrullDim (MvPolynomial σ ℤ ⧸ RingHom.ker φ) = (s : WithBot ℕ∞) + 1 := by
  set P := RingHom.ker φ
  have hPp : P.IsPrime := RingHom.ker_isPrime φ
  have hP : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0 := by
    intro m hm
    rw [RingHom.mem_ker, map_C_int] at hm
    exact_mod_cast (algebraMap ℚ L).injective (hm.trans (map_zero _).symm)
  obtain ⟨-, hcomap, hdim⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP
  set ψ : MvPolynomial σ ℚ →ₐ[ℚ] L := aeval fun v ↦ φ (X v)
  have hψ : (ψ : MvPolynomial σ ℚ →+* L).comp (MvPolynomial.map (Int.castRingHom ℚ)) = φ :=
    MvPolynomial.ringHom_ext (fun m ↦ by simp [ψ]) (fun v ↦ by simp [ψ])
  have hker : RingHom.ker ψ = ReciprocityTheory.AnForm.R.extQ P := by
    apply (IsLocalization.orderEmbedding (ReciprocityTheory.AnForm.R.IntegerToRational.intS σ) (MvPolynomial σ ℚ)).injective
    change (RingHom.ker (ψ : MvPolynomial σ ℚ →+* L)).comap (MvPolynomial.map (Int.castRingHom ℚ)) =
      (ReciprocityTheory.AnForm.R.extQ P).comap (MvPolynomial.map (Int.castRingHom ℚ))
    rw [RingHom.comap_ker, hψ]
    exact hcomap.symm
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨s, hs1, hs2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℚ) (A := MvPolynomial σ ℚ ⧸ RingHom.ker ψ)
  refine ⟨s, ?_, ?_⟩
  · rw [← hs2]
    exact ((Ideal.quotientKerEquivRange ψ).trans (Subalgebra.equivOfEq _ _ (aeval_range _))).trdeg_eq.symm
  · rw [← hker] at hdim
    rw [← hdim, hs1]
end GroundTheory.Heights₂.Heights.TrdegAdjoin
