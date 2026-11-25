-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.actP_actP_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:45:47.359053+00:00
-- url     : https://prove2.me/submissions/f858eed1-bd23-49c6-80c0-dfcb980166b3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_actD_mul_eig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
section Mat
variable {O k : Type} [CommRing O] [CommRing k] {d : ℕ}
private theorem smul_mulVec_lemma {S : Type} [CommRing S] {m : ℕ} (e : S)
    (A : Matrix (Fin m) (Fin m) S) (v : Fin m → S) : (e • A).mulVec v = e • A.mulVec v := by
  funext i
  show ∑ j, (e • A) i j * v j = e * ∑ j, A i j * v j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show e * A i j * v j = e * (A i j * v j)
  ring
end Mat
section Pair
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]
end Pair
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution (B : FB R d O) (χ : O →+* k) {n n' : ℕ} (b : Fin n → O) (c : Fin n → k) (h : IsEqv χ b c)
    (b' : Fin n' → O) (c' : Fin n' → k) (ξ : (Fin d → k) × (Fin d → k)) :
    actP B b c (actP B b' c' ξ) = evD χ b' c' • actP B b c ξ := by
  show ((actD (EigA.dActH k B) b c).mulVec ((actD (EigA.dActH k B) b' c').mulVec ξ.1),
      (actD (EigA.dActS k B) b c).mulVec ((actD (EigA.dActS k B) b' c').mulVec ξ.2)) = _
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, actD_mul_eig (EigA.dActH k B) χ b c h b' c',
    actD_mul_eig (EigA.dActS k B) χ b c h b' c', smul_mulVec_lemma,
    smul_mulVec_lemma]
  rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
