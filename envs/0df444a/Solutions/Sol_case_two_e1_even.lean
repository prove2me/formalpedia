-- Prove2me | solution 1 for case_two_e1_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:49:43.011606+00:00
-- url     : https://prove2.me/submissions/353376d9-3335-4757-9d9b-9e7070d52715

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_isUnit_intCast_of_natAbs_coprime
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ


section
open Finset Pointwise
section Case2_MultipleCycles
variable {m : ℕ} {a b : ℤ}
local notation "d₁" => Nat.gcd b.natAbs m
local notation "d₂" => Nat.gcd (Int.natAbs (b - a)) m
local notation "e₁" => m / d₁
private lemma intCast_2ba_eq :
    ((2 * b - a : ℤ) : ZMod m) = ((b - a : ℤ) : ZMod m) + ((b : ℤ) : ZMod m) := by grind
private lemma ZMod.val_add_one {n : ℕ} [NeZero n] (x : ZMod n) : (x + 1).val = (x.val + 1) % n := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
private lemma zmod_val_add_one (d : ℕ) [NeZero d] (i : ZMod d) :
    (i + 1).val = if i.val + 1 < d then i.val + 1 else 0 := by
  grind [ZMod.val_add_one, Nat.mod_eq_of_lt, Nat.mod_self]
private lemma parity_flip_even (e : ℕ) [NeZero e] (he : Even e)
    (j : ZMod e) : j.val % 2 ≠ (j + 1).val % 2 := by grind [zmod_val_add_one e j]
private lemma color_covers_even (d e : ℕ) [NeZero d] [NeZero e] (hd_ge2 : d ≥ 2)
    (hparity : ∀ j : ZMod e, j.val % 2 ≠ (j + 1).val % 2)
    (i : ZMod d) (j₁ j₂ : ZMod e) (k : Fin 3) :
    k = cycle_coloring d e (i, j₁) ∨
    k = cycle_coloring d e (i, j₁ + 1) ∨
    k = cycle_coloring d e (i + 1, j₂) ∨
    k = cycle_coloring d e (i + 1, j₂ + 1) := by
  grind [cycle_coloring, Fin.ext_iff, zmod_val_add_one]
section OrbitFramework
private lemma orbitMap_shift_b [NeZero m] (he1_b_zero : e₁ • (b : ZMod m) = 0) :
    ∀ p : ZMod d₁ × ZMod e₁, orbitMap m a b p + (b : ZMod m) = orbitMap m a b (p.1, p.2 + 1) := by
  intro ⟨i, j⟩
  simp only [orbitMap]
  by_cases hj : j.val + 1 < e₁
  · have hv : (j + 1).val = j.val + 1 := by rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hj
    rw [hv]
    grind
  · have hje : j.val + 1 = e₁ := by grind [ZMod.val_lt]
    have hv : (j + 1).val = 0 := by rw [ZMod.val_add_one, hje, Nat.mod_self]
    have h1 : (j.val : ZMod m) * ↑b + ↑b = 0 := by
      rw [← add_one_mul, ← Nat.cast_one, ← Nat.cast_add, hje, ← nsmul_eq_mul, he1_b_zero]
    rw [hv, Nat.cast_zero, zero_mul, add_zero, add_assoc, h1, add_zero]
private lemma orbitMap_cycle_index [NeZero m]
    (u : (ZMod d₁)ˣ) (hu : ↑u = ((b - a : ℤ) : ZMod d₁)) (i : ZMod d₁) (j : ZMod e₁) :
    ZMod.castHom d₁_dvd_m (ZMod d₁) (orbitMap m a b (i, j)) * u⁻¹ = i := by
  simp only [orbitMap, map_add, map_mul, map_natCast, map_intCast, b_zero_mod_d1, mul_zero,
    add_zero, mul_assoc, ← hu, Units.mul_inv, mul_one]
  simp [ZMod.natCast_val]
private lemma cycle_index_shift_ba [NeZero m]
    (u : (ZMod d₁)ˣ) (hu : ↑u = ((b - a : ℤ) : ZMod d₁)) (x : ZMod m) :
    ZMod.castHom d₁_dvd_m (ZMod d₁) (x + ↑(b - a)) * u⁻¹ =
    ZMod.castHom d₁_dvd_m (ZMod d₁) x * u⁻¹ + 1 := by
  simp only [map_add, map_intCast, add_mul, ← hu, Units.mul_inv]
private lemma equiv_symm_shift_b {γ : Type*} [AddCommMonoid γ]
    (Φ : ZMod d₁ × ZMod e₁ ≃ γ) {b : γ}
    (hΦ : ∀ i : ZMod d₁, ∀ j : ZMod e₁, Φ (i, j + 1) = Φ (i, j) + b) (x : γ) :
    Φ.symm (x + b) = ((Φ.symm x).1, (Φ.symm x).2 + 1) := by grind
private lemma equiv_symm_fst_eq {γ : Type*} (Φ : ZMod d₁ × ZMod e₁ ≃ γ) (α : γ → ZMod d₁)
    (hα : ∀ i : ZMod d₁, ∀ j : ZMod e₁, α (Φ (i, j)) = i) (x : γ) :
    (Φ.symm x).1 = α x := by grind
private lemma orbitEquiv_shift_b [NeZero m] {h_gcd_coprime : Nat.gcd d₁ d₂ = 1} (x : ZMod m) :
    (orbitEquiv h_gcd_coprime).symm (x + ↑b) =
    (((orbitEquiv h_gcd_coprime).symm x).1, ((orbitEquiv h_gcd_coprime).symm x).2 + 1) :=
  equiv_symm_shift_b _ (fun i j =>
    (orbitMap_shift_b (addOrderOf_b_eq (b := b) (m := m) ▸
      addOrderOf_nsmul_eq_zero _) (i, j)).symm) x
private lemma orbitEquiv_cycle_shift [NeZero m] {h_gcd_coprime : Nat.gcd d₁ d₂ = 1} (x : ZMod m) :
    ((orbitEquiv h_gcd_coprime).symm (x + ↑(b - a))).1 =
    ((orbitEquiv h_gcd_coprime).symm x).1 + 1 := by
  have hba_unit := isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 h_gcd_coprime)
  let u_ba := hba_unit.choose
  have hu_ba : ↑u_ba = ((b - a : ℤ) : ZMod d₁) := hba_unit.choose_spec
  let α : ZMod m → ZMod d₁ := fun x => ZMod.castHom d₁_dvd_m (ZMod d₁) x * u_ba⁻¹
  have hΦ_cycle := equiv_symm_fst_eq (orbitEquiv h_gcd_coprime) α (orbitMap_cycle_index u_ba hu_ba)
  rw [hΦ_cycle (x + ↑(b - a))]
  dsimp only [α]
  rw [cycle_index_shift_ba u_ba hu_ba]
  grind
private lemma orbit_coloring_polychrom (Φ : ZMod d₁ × ZMod e₁ ≃ ZMod m)
    (hΦ_add_b : ∀ x : ZMod m, Φ.symm (x + ↑b) = ((Φ.symm x).1, (Φ.symm x).2 + 1))
    (hΦ_cycle_shift : ∀ x : ZMod m, (Φ.symm (x + ↑(b - a))).1 = (Φ.symm x).1 + 1)
    (f : ZMod d₁ × ZMod e₁ → Fin 3) (hcovers : ∀ (n : ZMod m) (k : Fin 3),
      k = f ((Φ.symm n).1, (Φ.symm n).2) ∨
      k = f ((Φ.symm n).1, (Φ.symm n).2 + 1) ∨
      k = f ((Φ.symm n).1 + 1, (Φ.symm (n + ↑(b - a))).2) ∨
      k = f ((Φ.symm n).1 + 1, (Φ.symm (n + ↑(b - a))).2 + 1)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  let χ : ZMod m → Fin 3 := f ∘ Φ.symm
  refine ⟨χ, fun n k => ?_⟩
  simp only [zmod_set, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton]
  set i := (Φ.symm n).1
  set j := (Φ.symm n).2
  set j' := (Φ.symm (n + ↑(b - a))).2
  have hχ_n : χ n = f (i, j) := rfl
  have hχ_nb : χ (n + ↑b) = f (i, j + 1) := congr_arg f (hΦ_add_b n)
  have hχ_nba : χ (n + ↑(b - a)) = f (i + 1, j') := congr_arg f (Prod.ext (hΦ_cycle_shift n) rfl)
  have hχ_n2ba : χ (n + ↑(2 * b - a)) = f (i + 1, j' + 1) := by
    have : (n : ZMod m) + ↑(2 * b - a) = (n + ↑(b - a)) + ↑b := by rw [intCast_2ba_eq, add_assoc]
    grind
  rcases hcovers n k with h | h | h | h
  · exact ⟨0, by simp, by rw [add_zero, hχ_n, h]⟩
  all_goals grind
end OrbitFramework
end Case2_MultipleCycles
end

set_option autoImplicit true
open Finset Pointwise
variable {m : ℕ} {a b : ℤ}
local notation "d₁" => Nat.gcd b.natAbs m
local notation "d₂" => Nat.gcd (Int.natAbs (b - a)) m
local notation "e₁" => m / d₁
theorem _root_.solution (hm : m ≥ 289) (h_gcd_coprime : Nat.gcd d₁ d₂ = 1)
    (h_min : min d₁ d₂ > 1) (he1_even : Even e₁) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  haveI : NeZero m := ⟨by omega⟩
  exact orbit_coloring_polychrom (orbitEquiv h_gcd_coprime) orbitEquiv_shift_b
    orbitEquiv_cycle_shift (cycle_coloring d₁ e₁)
    (fun n k => color_covers_even d₁ e₁ (by grind) (parity_flip_even e₁ he1_even) _ _ _ k)
