-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.actP_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:26:09.403799+00:00
-- url     : https://prove2.me/submissions/c0bc49ef-a606-422f-b9a1-613947d22773

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_eig_actD
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
theorem _root_.solution (B : FB R d O) (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k) (h : IsEqv χ b c)
    (ξ : (Fin d → k) × (Fin d → k)) (a : O) : OactH k B a (actP B b c ξ) = χ a • actP B b c ξ := by
  have e1 := eig_actD (EigA.dActH k B) χ b c h a
  have e2 := eig_actD (EigA.dActS k B) χ b c h a
  show ((EigA.dActH k B a).mulVec ((actD (EigA.dActH k B) b c).mulVec ξ.1),
      (EigA.dActS k B a).mulVec ((actD (EigA.dActS k B) b c).mulVec ξ.2)) = _
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1, e2, smul_mulVec_lemma,
    smul_mulVec_lemma]
  rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
