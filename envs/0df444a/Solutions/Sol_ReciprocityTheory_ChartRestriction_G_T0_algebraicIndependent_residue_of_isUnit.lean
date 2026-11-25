-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.algebraicIndependent_residue_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:38.920027+00:00
-- url     : https://prove2.me/submissions/53148fb0-6b86-43f2-a251-14199be72b25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {A R E : Type} [CommRing A] [Field R] [Field E] (V : ValuationSubring E)
    [Algebra R (IsLocalRing.ResidueField V)] (φ : A →+* V) (ψ : A →+* R)
    (hψ : Function.Surjective ψ)
    (hc : ∀ a, algebraMap R (IsLocalRing.ResidueField V) (ψ a) = IsLocalRing.residue V (φ a))
    {τ : Type} (t : τ → V) (h : ∀ q : MvPolynomial τ A, q.map ψ ≠ 0 → IsUnit (eval₂ φ t q)) :
    AlgebraicIndependent R (fun j => IsLocalRing.residue V (t j)) := by
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hne
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective ψ hψ P
  have hu := (h q hne).map (IsLocalRing.residue V)
  have key : IsLocalRing.residue V (eval₂ φ t q) =
      MvPolynomial.aeval (fun j => IsLocalRing.residue V (t j)) (q.map ψ) := by
    rw [MvPolynomial.hom_eval₂, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
    exact RingHom.ext fun a => (hc a).symm
  rw [key, hP] at hu
  exact not_isUnit_zero hu
end ReciprocityTheory.ChartRestriction.G.T0
