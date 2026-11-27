-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.actD_mulVec_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:37:25.210283+00:00
-- url     : https://prove2.me/submissions/63434e5f-0a5a-4d5a-88ab-bef7195017ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
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
variable {O k : Type} [CommRing O] [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k)
    (v : Fin d → k) (hv : ∀ a, (M a).mulVec v = χ a • v) : (actD M b c).mulVec v = evD χ b c • v := by
  have key : ∀ s : Finset (Fin n),
      (∑ i ∈ s, c i • M (b i)).mulVec v = ∑ i ∈ s, (c i * χ (b i)) • v := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj ih
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.add_mulVec, ih,
        smul_mulVec_lemma, hv, smul_smul]
  unfold actD evD
  rw [key, Finset.sum_smul]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
