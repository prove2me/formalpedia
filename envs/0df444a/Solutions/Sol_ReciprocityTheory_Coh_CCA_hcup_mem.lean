-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.hcup_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:45:27.578453+00:00
-- url     : https://prove2.me/submissions/773a24f8-5c50-4216-95df-fb7e5336abe4

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] {X : Type u}
    [TopologicalSpace X] [MulAction K X] {M N P : TRep R K} (b : Pairing M N P) (p q : ℕ)
    (F : (Fin (p + 1) → X) → M.V) (F' : (Fin (q + 1) → X) → N.V) (hF : F ∈ hcoch M X p)
    (hF' : F' ∈ hcoch N X q) : hcup b.β p q F F' ∈ hcoch P X (p + q) := by
  simp only [hcoch] at hF hF' ⊢
  refine ⟨?_, fun g x => ?_⟩
  · have h1 : Continuous (fun x : Fin (p + q + 1) → X => F fun i : Fin (p + 1) => x ⟨i, by omega⟩) :=
      hF.1.comp (continuous_pi fun i => continuous_apply _)
    have h2 : Continuous
        (fun x : Fin (p + q + 1) → X => F' fun j : Fin (q + 1) => x ⟨p + j, by omega⟩) :=
      hF'.1.comp (continuous_pi fun j => continuous_apply _)
    exact b.cont.comp (h1.prodMk h2)
  · simp only [hcup]
    rw [hF.2 g (fun i => x ⟨i, by omega⟩), hF'.2 g (fun j => x ⟨p + j, by omega⟩), b.equiv]
end ReciprocityTheory.Coh.CCA
