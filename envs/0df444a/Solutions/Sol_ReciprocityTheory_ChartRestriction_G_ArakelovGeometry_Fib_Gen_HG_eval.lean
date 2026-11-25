-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.HG_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:49.28504+00:00
-- url     : https://prove2.me/submissions/b9dc3770-cfb1-4457-9c95-5565308f2b21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__homog_a4d5e8660c60
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ}
variable {x : ι → Ω} {e : Fin (D + 1) → ι}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
namespace Gen
theorem _root_.solution [DecidableEq ι] (G : Gen x e) {S : Type*} [Field S]
    (ψ : MvPolynomial (Fin (D + 1)) ℤ →+* S) (t : S) (hd : ψ G.dd ≠ 0) (F : MvPolynomial ι ℤ) :
    (G.HG F).eval₂ ψ t =
      ψ G.dd ^ F.totalDegree * MvPolynomial.eval₂ (Int.castRingHom S) (G.evQ ψ t) F := by
  have h1 : (G.HG F).eval₂ ψ t = MvPolynomial.eval₂ (Int.castRingHom S)
      (fun o : Option ι => (o.elim (Polynomial.C G.dd) G.Q).eval₂ ψ t)
      (homog none F.totalDegree (rename some F)) := by
    rw [Gen.HG, ← Polynomial.coe_eval₂RingHom, MvPolynomial.eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  have hv : (fun o : Option ι => (o.elim (Polynomial.C G.dd) G.Q).eval₂ ψ t) none ≠ 0 := by
    simpa using hd
  rw [h1, eval₂_homog _ none hv _ (totalDegree_rename_le _ _)]
  simp only [Option.elim, Polynomial.eval₂_C]
  congr 1
  rw [deh_apply, eval₂_rename]
  congr 1
  funext i
  simp [Gen.evQ, Polynomial.eval₂_C]
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
