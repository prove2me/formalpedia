-- Prove2me | solution 1 for case_two_odd_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:49:51.54349+00:00
-- url     : https://prove2.me/submissions/7908c685-2a09-41a6-9466-e98c3937b205

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
private lemma orbitMap_shift_ba [NeZero m] (i : ZMod d₁) (j : ZMod e₁) (hi : i.val + 1 < d₁) :
    orbitMap m a b (i, j) + ((b - a : ℤ) : ZMod m) = orbitMap m a b (i + 1, j) := by
  simp only [orbitMap, zmod_val_add_one, if_pos hi]
  push_cast
  ring
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
private lemma orbitEquiv_snd_shift_ba [NeZero m] {h_gcd_coprime : Nat.gcd d₁ d₂ = 1}
    (n : ZMod m) (hi : (orbitEquiv h_gcd_coprime).symm n |>.1.val + 1 < d₁) :
    ((orbitEquiv h_gcd_coprime).symm (n + ↑(b - a))).2 = ((orbitEquiv h_gcd_coprime).symm n).2 := by
  set Φ := orbitEquiv h_gcd_coprime
  set i := (Φ.symm n).1
  set j := (Φ.symm n).2
  have hshift := orbitMap_shift_ba (a := a) i j hi
  have hn : Φ (i, j) = n := Prod.eta (Φ.symm n) ▸ Equiv.apply_symm_apply Φ n
  have hΦ : Φ (i + 1, j) = n + ↑(b - a) := by
    simp only [Φ, orbitEquiv, Equiv.ofBijective_apply] at hn ⊢
    grind
  rw [← hΦ, Φ.symm_apply_apply]
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
private lemma cover_mod3_general (p₁ p₂ : Fin 3) (j₁ j₂ : ℕ)
    (hne : (j₁ + p₁.val) % 3 ≠ (j₂ + p₂.val) % 3) (k : Fin 3) :
    k = ⟨(j₁ + p₁.val) % 3, Nat.mod_lt _ (by grind)⟩ ∨
    k = ⟨(j₁ + 1 + p₁.val) % 3, Nat.mod_lt _ (by grind)⟩ ∨
    k = ⟨(j₂ + p₂.val) % 3, Nat.mod_lt _ (by grind)⟩ ∨
    k = ⟨(j₂ + 1 + p₂.val) % 3, Nat.mod_lt _ (by grind)⟩ := by
  by_contra! hall
  obtain ⟨h1, h2, h3, h4⟩ := hall
  grind [Fin.ext_iff]
private lemma case2c_nonwrap_hyp (d k₀ i j : ℕ) (hd : d ≥ 3)
    (hd_odd : Odd d) (hi : i + 1 < d) : (j + (case2c_pattern d k₀ i).val) % 3 ≠
    (j + (case2c_pattern d k₀ (i + 1)).val) % 3 := by grind [case2c_pattern]
private lemma case2c_wrap_hyp (d k₀ j : ℕ) (hd : d ≥ 3) (hd_odd : Odd d) :
    (j + (case2c_pattern d k₀ (d - 1)).val) % 3 ≠
    (j + k₀ + (case2c_pattern d k₀ 0).val) % 3 := by grind [case2c_pattern]
private lemma case2d_wrap_shift [NeZero m] (h_gcd_coprime : Nat.gcd d₁ d₂ = 1) :
    ∃ k₀ : ZMod e₁, (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m) := by
  set Φ := orbitEquiv h_gcd_coprime
  set q := Φ.symm ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
  have hq_i : q.1 = 0 := by
    set f := ZMod.castHom d₁_dvd_m (ZMod d₁)
    have hfφ : f (Φ q) = q.1 * ((b - a : ℤ) : ZMod d₁) := by
      change f (orbitMap m a b q) = _
      simp only [orbitMap, map_add, map_mul, map_natCast, map_intCast,
        b_zero_mod_d1, mul_zero, add_zero]
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [Equiv.apply_symm_apply] at hfφ
    have : f (d₁ • ((b - a : ℤ) : ZMod m)) = 0 := by
      rw [nsmul_eq_mul, map_mul, map_natCast, map_intCast, ZMod.natCast_self, zero_mul]
    rw [this] at hfφ
    exact (isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 h_gcd_coprime)).mul_left_eq_zero.mp
      hfφ.symm
  refine ⟨q.2, ?_⟩
  have hφq := Equiv.apply_symm_apply Φ ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
  change orbitMap m a b q = _ at hφq
  simp only [orbitMap] at hφq
  rw [(Prod.eta q).symm] at hφq
  simp only [hq_i, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add] at hφq
  grind
private lemma case2d_shift_ba_wrap [NeZero m] (he1_b_zero : e₁ • (b : ZMod m) = 0)
    (k₀ : ZMod e₁) (hk₀ : (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m))
    (i : ZMod d₁) (hi : i.val = d₁ - 1) : ∀ (j : ZMod e₁),
    orbitMap m a b (i, j) + ((b - a : ℤ) : ZMod m) = orbitMap m a b ((0 : ZMod d₁), j + k₀) := by
  intro j
  simp only [orbitMap, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add]
  have hpred : (d₁ - 1 + 1 : ℕ) = d₁ := Nat.succ_pred (NeZero.ne d₁)
  -- Step 1: rearrange i.val*(b-a) + j*b + (b-a) = d₁*(b-a) + j*b
  have hcast : (↑i.val : ZMod m) + 1 = (↑d₁ : ZMod m) := by
    rw [hi, ← Nat.cast_one (R := ZMod m), ← Nat.cast_add, hpred]
  have step1 : (↑i.val : ZMod m) * ((b - a : ℤ) : ZMod m) +
      ↑↑j.val * ((b : ℤ) : ZMod m) + ((b - a : ℤ) : ZMod m) =
      (↑d₁ : ZMod m) * ((b - a : ℤ) : ZMod m) + ↑↑j.val * ((b : ℤ) : ZMod m) := by grind
  rw [step1, ← nsmul_eq_mul (d₁), hk₀, nsmul_eq_mul, ← add_mul,
    ← Nat.cast_add (k₀.val) (j.val), ← nsmul_eq_mul, Nat.add_comm]
  -- Reduce (j+k₀) • b mod e₁ using he1_b_zero
  set n := j.val + k₀.val
  have h1 : (j + k₀).val = n % e₁ := ZMod.val_add j k₀
  rw [h1]
  conv_lhs => rw [(Nat.div_add_mod n e₁).symm]
  rw [add_nsmul, mul_nsmul, he1_b_zero, smul_zero, zero_add, nsmul_eq_mul]
private lemma orbitEquiv_snd_shift_ba_wrap [NeZero m]
    {h_gcd_coprime : Nat.gcd d₁ d₂ = 1} (he1_b_zero : e₁ • (b : ZMod m) = 0)
    (k₀ : ZMod e₁) (hk₀ : (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m))
    (n : ZMod m) (hi : (orbitEquiv h_gcd_coprime).symm n |>.1.val = d₁ - 1) :
    ((orbitEquiv h_gcd_coprime).symm (n + ↑(b - a))).2 =
    ((orbitEquiv h_gcd_coprime).symm n).2 + k₀ := by
  set Φ := orbitEquiv h_gcd_coprime
  set i := (Φ.symm n).1
  set j := (Φ.symm n).2
  have hshift := case2d_shift_ba_wrap he1_b_zero k₀ hk₀ i hi
  have hn : Φ (i, j) = n := Prod.eta (Φ.symm n) ▸ Equiv.apply_symm_apply Φ n
  have hΦ : Φ ((0 : ZMod d₁), j + k₀) = n + ↑(b - a) := by
    simp only [Φ, orbitEquiv, Equiv.ofBijective_apply] at hn ⊢
    grind
  grind
private lemma case2c_mod3 (h3e : 3 ∣ e₁) (x y : ℕ) : (x % e₁ + y) % 3 = (x + y) % 3 := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd x h3e, ← Nat.add_mod]
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
    (h_min : min d₁ d₂ > 1) (hd1_odd : Odd d₁) (he1_div3 : 3 ∣ e₁) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  haveI : NeZero m := ⟨by omega⟩
  have he1_b_zero : e₁ • (b : ZMod m) = 0 :=
    addOrderOf_b_eq (b := b) (m := m) ▸ addOrderOf_nsmul_eq_zero _
  let Φ := orbitEquiv h_gcd_coprime
  obtain ⟨k₀, hk₀⟩ := case2d_wrap_shift h_gcd_coprime
  have hd1_ge3 : d₁ ≥ 3 := by grind
  let f : ZMod d₁ × ZMod e₁ → Fin 3 := fun ⟨i, j⟩ =>
    ⟨(j.val + (case2c_pattern d₁ k₀.val i.val).val) % 3, Nat.mod_lt _ (by grind)⟩
  exact orbit_coloring_polychrom Φ orbitEquiv_shift_b orbitEquiv_cycle_shift f (fun n k => by
    set i := (Φ.symm n).1
    set j := (Φ.symm n).2
    set j' := (Φ.symm (n + ↑(b - a))).2
    set p := case2c_pattern d₁ k₀.val i.val
    by_cases hi : i.val + 1 < d₁
    · have hj'_eq : j' = j := orbitEquiv_snd_shift_ba n hi
      rw [hj'_eq]
      set p' := case2c_pattern d₁ k₀.val (i + 1).val
      have hi'_eq : (i + 1).val = i.val + 1 := by rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hi
      have hhyp : (j.val + p.val) % 3 ≠ (j.val + p'.val) % 3 := by
        change (j.val + (case2c_pattern d₁ k₀.val i.val).val) % 3 ≠
          (j.val + (case2c_pattern d₁ k₀.val (i + 1).val).val) % 3
        rw [hi'_eq]
        exact case2c_nonwrap_hyp d₁ k₀.val i.val j.val hd1_ge3 hd1_odd hi
      have hp : p = case2c_pattern d₁ k₀.val i.val := rfl
      have hp' : p' = case2c_pattern d₁ k₀.val (i.val + 1) := by simp [p', hi'_eq]
      rcases cover_mod3_general p p' j.val j.val hhyp k with h | h | h | h
      · grind
      · refine Or.inr (Or.inl ?_)
        rw [h, hp]
        exact Fin.ext (by simp [f, ZMod.val_add_one, case2c_mod3 he1_div3])
      · grind
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [h, hp']
        exact Fin.ext (by simp [f, ZMod.val_add_one, case2c_mod3 he1_div3, Nat.mod_eq_of_lt hi])
    · have hi_eq : i.val = d₁ - 1 := by grind [ZMod.val_lt]
      have hj'_eq : j' = j + k₀ :=
        orbitEquiv_snd_shift_ba_wrap he1_b_zero k₀ hk₀ n hi_eq
      rw [hj'_eq]
      set p₀ := case2c_pattern d₁ k₀.val 0
      have hp_eq : p = case2c_pattern d₁ k₀.val (d₁ - 1) := by grind
      have hhyp : (j.val + p.val) % 3 ≠ (j.val + k₀.val + p₀.val) % 3 := by
        rw [hp_eq]
        exact case2c_wrap_hyp d₁ k₀.val j.val hd1_ge3 hd1_odd
      have hj'_val : (j + k₀).val = (j.val + k₀.val) % e₁ := ZMod.val_add j k₀
      have hi1_val : (i + 1).val = 0 := by rw [ZMod.val_add_one, hi_eq]; grind [Nat.mod_self]
      have hp : p = case2c_pattern d₁ k₀.val i.val := rfl
      have hp₀_val : (↑p₀ : ℕ) = ↑(case2c_pattern d₁ k₀.val 0) := rfl
      rcases cover_mod3_general p p₀ j.val (j.val + k₀.val) hhyp k with h | h | h | h
      · grind
      · refine Or.inr (Or.inl ?_)
        rw [h, hp]
        exact Fin.ext (by simp [f, ZMod.val_add_one, case2c_mod3 he1_div3])
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [h]
        refine Fin.ext ?_
        simp only [f, hi1_val]
        rw [hj'_val]
        exact (case2c_mod3 he1_div3 (j.val + k₀.val) p₀.val).symm
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [h]
        refine Fin.ext ?_
        simp only [f, hi1_val, ZMod.val_add_one]
        rw [hj'_val, hp₀_val]
        simp only [case2c_mod3 he1_div3, Nat.add_assoc])
