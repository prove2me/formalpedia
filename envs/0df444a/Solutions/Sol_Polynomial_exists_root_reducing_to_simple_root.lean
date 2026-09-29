-- Prove2me | solution 1 for Polynomial.exists_root_reducing_to_simple_root
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/564789ec-89ec-51a6-9b8f-5f4db6e94315

import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_root_reducing_to_simple_root

set_option autoImplicit false

open Polynomial

namespace S09RD

variable {A k : Type*} [CommRing A] [CommRing k]

theorem map_prod_X_sub_C (red : A →+* k) (s : Multiset A) :
    (s.map fun a => X - C a).prod.map red = ((s.map red).map fun c => X - C c).prod := by
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp [Function.comp]

variable [IsDomain A] [IsDomain k]

omit [IsDomain A] in

theorem rootMultiplicity_map_eq_count [DecidableEq k] (red : A →+* k) (s : Multiset A) (b : k) :
    ((s.map fun a => X - C a).prod.map red).rootMultiplicity b = (s.map red).count b := by
  rw [map_prod_X_sub_C, ← count_roots, roots_multiset_prod_X_sub_C]

theorem rootMultiplicity_prod_eq_count [DecidableEq A] (s : Multiset A) (a : A) :
    (s.map fun a => X - C a).prod.rootMultiplicity a = s.count a := by
  rw [← count_roots, roots_multiset_prod_X_sub_C]

theorem exists_root_of_rootMultiplicity_map_eq_one (red : A →+* k) (s : Multiset A) (b : k)
    (hb : ((s.map fun a => X - C a).prod.map red).rootMultiplicity b = 1) :
    ∃ a ∈ s, red a = b ∧ (s.map fun a => X - C a).prod.rootMultiplicity a = 1 ∧
      ∀ a' ∈ s, red a' = b → a' = a := by
  classical
  rw [rootMultiplicity_map_eq_count] at hb
  have hmem : b ∈ s.map red := Multiset.count_pos.mp (by rw [hb]; exact Nat.one_pos)
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hmem
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [Multiset.map_cons, Multiset.count_cons_self] at hb
  have ht : red a ∉ t.map red := Multiset.count_eq_zero.mp (by omega)
  have hat : a ∉ t := fun h => ht (Multiset.mem_map_of_mem red h)
  refine ⟨a, Multiset.mem_cons_self a t, rfl, ?_, ?_⟩
  · rw [rootMultiplicity_prod_eq_count, Multiset.count_cons_self, Multiset.count_eq_zero.mpr hat]
  · intro a' ha' hred
    rcases Multiset.mem_cons.mp ha' with h | h
    · exact h
    · exact absurd (hred ▸ Multiset.mem_map_of_mem red h) ht

end S09RD

theorem solution {A k : Type*} [CommRing A] [IsDomain A] [CommRing k] [IsDomain k] (red : A →+* k) (s : Multiset A) (b : k) (hb : ((s.map fun a => Polynomial.X - Polynomial.C a).prod.map red).rootMultiplicity b = 1) : ∃ a ∈ s, red a = b ∧ (s.map fun a => Polynomial.X - Polynomial.C a).prod.rootMultiplicity a = 1 ∧ ∀ a' ∈ s, red a' = b → a' = a := by
  exact S09RD.exists_root_of_rootMultiplicity_map_eq_one red s b hb

end S_Polynomial_exists_root_reducing_to_simple_root
end P2MW
export P2MW.S_Polynomial_exists_root_reducing_to_simple_root (solution)
