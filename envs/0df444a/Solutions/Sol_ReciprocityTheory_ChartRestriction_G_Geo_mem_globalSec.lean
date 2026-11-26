-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.mem_globalSec
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:26:35.13588+00:00
-- url     : https://prove2.me/submissions/3bb06077-9b80-4e2a-8863-d85a59779681

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable (o : Type*) {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι : Type*}
variable {o}
theorem _root_.solution {x : ι → Ω} {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (B : ChartBundle o x r E) (e : E) :
    e ∈ globalSec B ↔ ∀ i, x i ≠ 0 → e ∈ B.lat i := by
  first
    | (intros; simp [ChartBundle, globalSec])
    | (intros; unfold ChartBundle globalSec; simp)
    | (intros; simp [ChartBundle, globalSec]; done)
    | (intros; ext; simp [ChartBundle, globalSec])
    | (intros; simp only [ChartBundle, globalSec]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [ChartBundle, globalSec])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [ChartBundle, globalSec])
    | (intros; unfold ChartBundle globalSec; split_ifs <;> simp_all)
    | (intros; unfold ChartBundle globalSec; positivity)
    | (intros; unfold ChartBundle globalSec; ring)
    | (intros; unfold ChartBundle globalSec; exact?)
    | (intros; aesop (add norm simp [ChartBundle, globalSec]))
    | (intros; simp [ChartBundle, globalSec] <;> aesop)
    | (intros; exact ChartBundle.symm ..)
    | (intros; exact ChartBundle.comm ..)
    | (intros; exact globalSec.symm ..)
    | (intros; exact globalSec.comm ..)
  trace "HIT_191_0"

end 
