-- Prove2me | solution 1 for R03SP02P3FactorAssignmentTransportV1.assignment_of_p3Factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:54:49.808824+00:00
-- url     : https://prove2.me/submissions/364fcb46-1f79-4c82-a023-011d3ed1ea25

import Definitions.Def_cubic_p3_partition_models

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace R03SP02P3FactorAssignmentTransportV1

open CubicP3Partition

noncomputable section

/-- A finite exact-cover assignment already contains precisely the placement
shape required by the frozen `P3Factor` structure. -/
theorem p3Factor_of_bijective_assignment
    {G : SimpleGraph (Fin 12)}
    (place : Fin 4 × Fin 3 → Fin 12)
    (hbij : Function.Bijective place)
    (hedge01 : ∀ i : Fin 4, G.Adj (place (i, 0)) (place (i, 1)))
    (hedge12 : ∀ i : Fin 4, G.Adj (place (i, 1)) (place (i, 2))) :
    Nonempty (P3Factor G) := by
  let e : (Fin 4 × Fin 3) ≃ Fin 12 := Equiv.ofBijective place hbij
  exact ⟨{
    blockCount := 4
    place := e
    edge01 := hedge01
    edge12 := hedge12
  }⟩


end
end R03SP02P3FactorAssignmentTransportV1

open R03SP02P3FactorAssignmentTransportV1
open CubicP3Partition
theorem solution
    {G : SimpleGraph (Fin 12)}
    (f : P3Factor G) :
    ∃ place : Fin 4 × Fin 3 → Fin 12,
      Function.Bijective place ∧
      (∀ i : Fin 4, G.Adj (place (i, 0)) (place (i, 1))) ∧
      (∀ i : Fin 4, G.Adj (place (i, 1)) (place (i, 2))) := by
  have hcount : f.blockCount = 4 := by
    have hc : Fintype.card (Fin f.blockCount × Fin 3) = Fintype.card (Fin 12) :=
      Fintype.card_congr f.place
    simp at hc
    omega
  let c : Fin 4 ≃ Fin f.blockCount := finCongr hcount.symm
  let q : (Fin 4 × Fin 3) ≃ (Fin f.blockCount × Fin 3) :=
    Equiv.prodCongr c (Equiv.refl (Fin 3))
  let place : Fin 4 × Fin 3 → Fin 12 := f.place ∘ q
  have hplace : Function.Bijective place := f.place.bijective.comp q.bijective
  refine ⟨place, hplace, ?_, ?_⟩
  · intro i
    simpa [place, q, Function.comp_def] using f.edge01 (c i)
  · intro i
    simpa [place, q, Function.comp_def] using f.edge12 (c i)

