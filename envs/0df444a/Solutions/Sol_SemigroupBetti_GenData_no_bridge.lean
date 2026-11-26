-- Prove2me | solution 1 for SemigroupBetti.GenData.no_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:10:29.468799+00:00
-- url     : https://prove2.me/submissions/94125414-ad19-4286-af31-300abd94b566

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_GenData_comp_eq_of_mem
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_reachable_of_bridge
attribute [local simp] SemigroupBetti.GenData.mem_fiber



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) {z y b : Fin 4 → ℕ}
    (hz : G.nu z = d) (hy : G.nu y = d) (hb : G.nu b = d) {i j : Fin 4} (hi : i ∈ K)
    (hzi : 0 < z i) (hj : j ∉ K) (hyj : 0 < y j) (hbz : SharesVar b z) (hby : SharesVar b y) :
    False := by
  obtain ⟨C, C', hne, hC, hC'⟩ := hS
  let z' : G.fiber d := ⟨z, G.mem_fiber.2 hz⟩
  let y' : G.fiber d := ⟨y, G.mem_fiber.2 hy⟩
  have h1 : (G.nabla d).connectedComponentMk z' = C := G.comp_eq_of_mem z' (hC ▸ hi) hzi
  have h2 : (G.nabla d).connectedComponentMk y' = C' :=
    G.comp_eq_of_mem y' (by rw [hC']; exact mem_compl.2 hj) hyj
  apply hne
  rw [← h1, ← h2]
  exact SimpleGraph.ConnectedComponent.sound (G.reachable_of_bridge b hb hbz hby)
end SemigroupBetti.GenData
