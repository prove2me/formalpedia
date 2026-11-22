-- Prove2me | solution 1 for case_one_residues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:49:51.120579+00:00
-- url     : https://prove2.me/submissions/a90316b0-055e-4a6c-b56f-669800842a87

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Theorems.Thm_hasPolychromColouring_mul_unit
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_table1_0134
import Theorems.Thm_table1_0235
import Theorems.Thm_table1_0347
import Theorems.Thm_table1_0358
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ



set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)
theorem _root_.solution (g : ℕ) (hm : m ≥ 289) (h_res : m % 3 ≠ 0)
    (h_range : 2 * (m / 6) ≤ g ∧ g ≤ (m + 2) / 3) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨hl, hr⟩ := h_range
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
  rw [← hasPolychromColouring_mul_unit m u]
  -- Each branch computes 3g and 3(g+1) mod m, then matches to a table1 set.
  have h1 : m = 3 * g - 2 ∨ m = 3 * g - 1 ∨ m = 3 * g + 1 ∨
      m = 3 * g + 2 ∨ m = 3 * g + 4 ∨ m = 3 * g + 5 := by grind
  -- Helper for computing (3 * g : ZMod m) when m = 3g + k
  have cast_sub (k : ℕ) (hk : m = 3 * g - k) : (3 : ZMod m) * (g : ZMod m) = (k : ZMod m) := by
    have h : ((3 * g : ℕ) : ZMod m) = (m + k : ℕ) := by congr 1; omega
    push_cast [ZMod.natCast_self] at h; grind
  have cast_add (k : ℕ) (hk : m = 3 * g + k) : (3 : ZMod m) * (g : ZMod m) = -↑k := by
    have : ((3 * g + k : ℕ) : ZMod m) = (m : ℕ) := by rw [hk]
    push_cast [ZMod.natCast_self] at this
    grind
  rcases h1 with hg | hg | hg | hg | hg | hg
  · -- m = 3g - 2: {0,3,2,5} = {0,2,3,5}
    have h3g := cast_sub 2 hg
    have h3g1 : (3 : ZMod m) * ((g : ZMod m) + 1) = 5 := by grind
    simpa [hu, Nat.cast_ofNat, image_insert, mul_zero, mul_one, h3g, image_singleton,
      h3g1, insert_comm] using table1_0235 m (by grind)
  · -- m = 3g - 1: {0,3,1,4} = {0,1,3,4}
    have h3g := cast_sub 1 hg
    have h3g1 : (3 : ZMod m) * ((g : ZMod m) + 1) = 4 := by grind
    simpa [hu, Nat.cast_ofNat, image_insert, mul_zero, mul_one, h3g,
      image_singleton, h3g1, insert_comm] using table1_0134 m (by grind)
  · -- m = 3g + 1: {0,3,-1,2} = -1 +ᵥ {0,1,3,4}
    have h3g := cast_add 1 hg
    have h3g1 : (3 : ZMod m) * ((g : ZMod m) + 1) = 2 := by grind
    have : {0, (3 : ZMod m), -1, 2} = (-1 : ZMod m) +ᵥ ({0, 1, 3, 4} : Finset (ZMod m)) := by
      simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]; grind
    simpa [hu, h3g, h3g1, this] using table1_0134 m (by grind)
  · -- m = 3g + 2: {0,3,-2,1} = -2 +ᵥ {0,2,3,5}
    have h3g := cast_add 2 hg
    have h3g1 : (3 : ZMod m) * ((g : ZMod m) + 1) = 1 := by grind
    have : {0, (3 : ZMod m), -2, 1} = (-2 : ZMod m) +ᵥ ({0, 2, 3, 5} : Finset (ZMod m)) := by
      simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]; grind
    simpa [hu, h3g, h3g1, this] using table1_0235 m (by grind)
  · -- m = 3g + 4: {0,3,-4,-1} = -4 +ᵥ {0,3,4,7}
    have h3g := cast_add 4 hg
    have h3g1 : (3 : ZMod m) * ((g : ZMod m) + 1) = -1 := by grind
    have : {0, (3 : ZMod m), -4, -1} = (-4 : ZMod m) +ᵥ ({0, 3, 4, 7} : Finset (ZMod m)) := by
      simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]; grind
    simpa [hu, h3g, h3g1, this] using table1_0347 m (by grind)
  · -- m = 3g + 5: {0,3,-5,-2} = -5 +ᵥ {0,3,5,8}
    have h3g := cast_add 5 hg
    have h3g1 : (3 : ZMod m) * ((g : ZMod m) + 1) = -2 := by grind
    have : {0, (3 : ZMod m), -5, -2} = (-5 : ZMod m) +ᵥ ({0, 3, 5, 8} : Finset (ZMod m)) := by
      simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]; grind
    simpa [hu, h3g, h3g1, this] using table1_0358 m (by grind)
