-- Prove2me | solution 1 for Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/40ad2e01-db5f-5b64-9aa1-415aa2c63ba9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard

set_option autoImplicit false

namespace BrauerLiftSqZero

open Finset

variable {A B : Type*} [Ring A] [Ring B] (π : A →+* B)

def oneAdd (d : A) (hd : d * d = 0) : Aˣ where
  val := 1 + d
  inv := 1 - d
  val_inv := by
    have : (1 + d) * (1 - d) = 1 - d * d := by noncomm_ring
    rw [this, hd, sub_zero]
  inv_val := by
    have : (1 - d) * (1 + d) = 1 - d * d := by noncomm_ring
    rw [this, hd, sub_zero]

@[scoped simp] theorem val_oneAdd (d : A) (hd : d * d = 0) : ((oneAdd d hd : Aˣ) : A) = 1 + d := rfl

variable {π}

theorem exists_unit_lift (hπ : Function.Surjective π)
    (hker : ∀ x y : A, π x = 0 → π y = 0 → x * y = 0) (b : Bˣ) :
    ∃ a : Aˣ, Units.map (π : A →* B) a = b := by
  obtain ⟨x, hx⟩ := hπ (b : B)
  obtain ⟨y, hy⟩ := hπ (↑b⁻¹ : B)
  set e := x * y - 1 with he
  set e' := y * x - 1 with he'
  have hπe : π e = 0 := by simp [he, hx, hy]
  have hπe' : π e' = 0 := by simp [he', hx, hy]
  have hee : e * e = 0 := hker _ _ hπe hπe
  have hee' : e' * e' = 0 := hker _ _ hπe' hπe'
  have hxy : x * y = 1 + e := by simp [he]
  have hyx : y * x = 1 + e' := by simp [he']

  have hr : x * (y * (1 - e)) = 1 := by
    rw [← mul_assoc, hxy]
    have : (1 + e) * (1 - e) = 1 - e * e := by noncomm_ring
    rw [this, hee, sub_zero]
  have hl : ((1 - e') * y) * x = 1 := by
    rw [mul_assoc, hyx]
    have : (1 - e') * (1 + e') = 1 - e' * e' := by noncomm_ring
    rw [this, hee', sub_zero]
  have hlr : (1 - e') * y = y * (1 - e) := by
    calc (1 - e') * y = ((1 - e') * y) * (x * (y * (1 - e))) := by rw [hr, mul_one]
      _ = (((1 - e') * y) * x) * (y * (1 - e)) := by noncomm_ring
      _ = y * (1 - e) := by rw [hl, one_mul]
  refine ⟨⟨x, y * (1 - e), hr, ?_⟩, ?_⟩
  · rw [← hlr]; exact hl
  · ext; simp [hx]

section

variable {G : Type*} [Group G] [Fintype G]

private theorem _root_.BrauerLiftSqZero.exists_lift (hπ : Function.Surjective π)
    (hker : ∀ x y : A, π x = 0 → π y = 0 → x * y = 0)
    (hG : IsUnit ((Fintype.card G : ℕ) : A)) (ρbar : G →* Bˣ) :
    ∃ ρ : G →* Aˣ, (Units.map (π : A →* B)).comp ρ = ρbar := by
  classical

  choose s hs using fun g => exists_unit_lift hπ hker (ρbar g)

  obtain ⟨u, hu⟩ := hG
  set c : A := ((Fintype.card G : ℕ) : A) with hc
  set cinv : A := (↑u⁻¹ : A) with hcinv
  have hcomm : ∀ a : A, cinv * a = a * cinv := fun a => by
    have h1 : Commute (u : A) a := by rw [hu]; exact Nat.cast_commute _ _
    exact (h1.units_inv_left).eq
  have hcinv_c : cinv * c = 1 := by rw [hcinv, ← hu]; exact u.inv_mul

  set ε : G → G → A := fun g h => ((s g * s h * (s (g * h))⁻¹ : Aˣ) : A) - 1 with hε
  have hπs : ∀ g, π (s g : A) = (ρbar g : B) := fun g => by
    have := congrArg (fun v : Bˣ => (v : B)) (hs g)
    simpa using this
  have hπsinv : ∀ g, π ((s g)⁻¹ : Aˣ) = ((ρbar g)⁻¹ : Bˣ) := fun g => by
    have := congrArg (fun v : Bˣ => ((v⁻¹ : Bˣ) : B)) (hs g)
    simpa [Units.coe_map_inv] using this
  have hπε : ∀ g h, π (ε g h) = 0 := fun g h => by
    simp only [hε, map_sub, map_one, Units.val_mul, map_mul, hπs, hπsinv, map_mul ρbar]
    rw [← Units.val_mul, ← Units.val_mul]
    simp

  have E1 : ∀ g h, (s g : A) * s h = (1 + ε g h) * s (g * h) := fun g h => by
    simp only [hε, add_sub_cancel]
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]

  set κ : G → A → A := fun g a => (s g : A) * a * ((s g)⁻¹ : Aˣ) with hκ
  have E2 : ∀ g a, (s g : A) * a = κ g a * s g := fun g a => by
    simp only [hκ, Units.inv_mul_cancel_right]
  have hκadd : ∀ g a b, κ g (a + b) = κ g a + κ g b := fun g a b => by
    simp only [hκ, mul_add, add_mul]
  have hκone : ∀ g, κ g 1 = 1 := fun g => by simp [hκ]
  have hκneg : ∀ g a, κ g (-a) = -κ g a := fun g a => by simp [hκ]
  have hκsum : ∀ g (f : G → A), κ g (∑ t, f t) = ∑ t, κ g (f t) := fun g f => by
    simp only [hκ, Finset.mul_sum, Finset.sum_mul]
  have hκc : ∀ g a, κ g (cinv * a) = cinv * κ g a := fun g a => by
    simp only [hκ]
    rw [← mul_assoc (s g : A) cinv a, ← hcomm (s g : A)]
    simp only [mul_assoc]
  have hπκ : ∀ g a, π a = 0 → π (κ g a) = 0 := fun g a ha => by
    simp [hκ, ha]

  have E3 : ∀ g h t, ε g (h * t) + κ g (ε h t) = ε g h + ε (g * h) t := fun g h t => by
    have way1 : (s g : A) * s h * s t
        = (1 + κ g (ε h t)) * (1 + ε g (h * t)) * s (g * h * t) := by
      rw [mul_assoc (s g : A), E1 h t, ← mul_assoc (s g : A), E2 g, hκadd, hκone,
        mul_assoc _ (s g : A), E1 g (h * t), ← mul_assoc, mul_assoc g h t]
    have way2 : (s g : A) * s h * s t
        = (1 + ε g h) * (1 + ε (g * h) t) * s (g * h * t) := by
      rw [E1 g h, mul_assoc, E1 (g * h) t, ← mul_assoc]
    have hcancel : (1 + κ g (ε h t)) * (1 + ε g (h * t)) = (1 + ε g h) * (1 + ε (g * h) t) := by
      have := way1.symm.trans way2
      have h' := congrArg (fun a : A => a * ((s (g * h * t))⁻¹ : Aˣ)) this
      simpa only [Units.mul_inv_cancel_right] using h'
    have z1 : κ g (ε h t) * ε g (h * t) = 0 := hker _ _ (hπκ _ _ (hπε _ _)) (hπε _ _)
    have z2 : ε g h * ε (g * h) t = 0 := hker _ _ (hπε _ _) (hπε _ _)
    have ex1 : (1 + κ g (ε h t)) * (1 + ε g (h * t)) = 1 + (ε g (h * t) + κ g (ε h t)) := by
      rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, z1, add_zero, add_assoc,
        add_comm (ε g (h * t))]
    have ex2 : (1 + ε g h) * (1 + ε (g * h) t) = 1 + (ε g h + ε (g * h) t) := by
      rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, z2, add_zero, add_assoc,
        add_comm (ε (g * h) t)]
    have := hcancel
    rw [ex1, ex2] at this
    exact add_left_cancel this

  set Sε : G → A := fun g => ∑ t, ε g t with hSε
  have E3sum : ∀ g h, Sε g + κ g (Sε h) = c * ε g h + Sε (g * h) := fun g h => by
    have hsum := congrArg (fun f : G → A => ∑ t, f t) (funext fun t => E3 g h t)
    simp only [Finset.sum_add_distrib] at hsum
    have reidx : ∑ t, ε g (h * t) = ∑ t, ε g t :=
      Fintype.sum_bijective (fun t => h * t) (Group.mulLeft_bijective h) _ _ fun _ => rfl
    rw [reidx, ← hκsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    simpa [hSε, hc] using hsum
  have hπS : ∀ g, π (Sε g) = 0 := fun g => by
    simp [hSε, map_sum, hπε]

  set δ : G → A := fun g => -(cinv * Sε g) with hδ
  have hπδ : ∀ g, π (δ g) = 0 := fun g => by simp [hδ, hπS]
  have E4 : ∀ g h, δ g + κ g (δ h) + ε g h = δ (g * h) := fun g h => by
    simp only [hδ, hκneg, hκc]
    have := congrArg (fun a => cinv * a) (E3sum g h)
    simp only [mul_add, ← mul_assoc, hcinv_c, one_mul] at this

    have h' : cinv * Sε g + cinv * κ g (Sε h) - ε g h = cinv * Sε (g * h) := by
      rw [this]; abel
    rw [← h']; abel
  have hδδ : ∀ g, δ g * δ g = 0 := fun g => hker _ _ (hπδ g) (hπδ g)

  have expand : ∀ x y z : A, π x = 0 → π y = 0 → π z = 0 →
      (1 + x) * (1 + y) * (1 + z) = 1 + (x + y + z) := fun x y z hx hy hz => by
    have hxy := hker _ _ hx hy
    have hxz := hker _ _ hx hz
    have hyz := hker _ _ hy hz
    have : (1 + x) * (1 + y) * (1 + z)
        = 1 + (x + y + z) + (x * y + x * z + y * z + x * y * z) := by noncomm_ring
    rw [this, hxy, hxz, hyz, zero_mul]; abel

  let ρf : G → Aˣ := fun g => oneAdd (δ g) (hδδ g) * s g
  have hmul : ∀ g h, ρf (g * h) = ρf g * ρf h := fun g h => by
    ext
    simp only [ρf, Units.val_mul, val_oneAdd]
    symm
    calc (1 + δ g) * (s g : A) * ((1 + δ h) * s h)
        = (1 + δ g) * ((s g : A) * (1 + δ h)) * s h := by noncomm_ring
      _ = (1 + δ g) * (1 + κ g (δ h)) * ((s g : A) * s h) := by
          rw [E2 g (1 + δ h), hκadd, hκone]; noncomm_ring
      _ = (1 + δ g) * (1 + κ g (δ h)) * (1 + ε g h) * s (g * h) := by
          rw [E1 g h]; noncomm_ring
      _ = (1 + (δ g + κ g (δ h) + ε g h)) * s (g * h) := by
          rw [expand _ _ _ (hπδ g) (hπκ _ _ (hπδ h)) (hπε g h)]
      _ = (1 + δ (g * h)) * s (g * h) := by rw [E4]
  refine ⟨MonoidHom.mk' ρf hmul, ?_⟩
  ext g
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mk'_apply, Units.coe_map,
    MonoidHom.coe_coe, ρf, Units.val_mul, val_oneAdd, map_mul, map_add, map_one, hπδ, add_zero,
    one_mul, hπs]

p2m_export "BrauerLiftSqZero" "exists_lift"
end

theorem exists_lift' {G : Type*} [Group G] [Finite G] (hπ : Function.Surjective π)
    (hker : ∀ x y : A, π x = 0 → π y = 0 → x * y = 0)
    (hG : IsUnit ((Nat.card G : ℕ) : A)) (ρbar : G →* Bˣ) :
    ∃ ρ : G →* Aˣ, (Units.map (π : A →* B)).comp ρ = ρbar := by
  haveI := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hG
  exact exists_lift hπ hker hG ρbar

end BrauerLiftSqZero
p2m_reactivate "P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.BrauerLiftSqZero"

namespace BrauerLiftComplete

open Matrix

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {G : Type*} [Group G] [Finite G]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem le_pow_succ (i : ℕ) : I ^ (i + 2) ≤ I ^ (i + 1) := Ideal.pow_le_pow_right (by omega)

private def _root_.BrauerLiftComplete.trans (i : ℕ) : R ⧸ I ^ (i + 2) →+* R ⧸ I ^ (i + 1) := Ideal.Quotient.factor (le_pow_succ I i)

p2m_export "BrauerLiftComplete" "trans"
theorem trans_mk (i : ℕ) (x : R) : trans I i (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

theorem trans_surjective (i : ℕ) : Function.Surjective (trans I i) :=
  Ideal.Quotient.factor_surjective _

theorem trans_eq_zero_iff (i : ℕ) (x : R) :
    trans I i (Ideal.Quotient.mk _ x) = 0 ↔ x ∈ I ^ (i + 1) := by
  rw [trans_mk, Ideal.Quotient.eq_zero_iff_mem]

theorem mul_eq_zero_of_trans (i : ℕ) (u v : R ⧸ I ^ (i + 2)) (hu : trans I i u = 0)
    (hv : trans I i v = 0) : u * v = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [trans_eq_zero_iff] at hu hv
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hab : a * b ∈ I ^ (i + 1 + (i + 1)) := by
    rw [pow_add]; exact Ideal.mul_mem_mul hu hv
  exact Ideal.pow_le_pow_right (by omega) hab

def Trans (i : ℕ) : Matrix n n (R ⧸ I ^ (i + 2)) →+* Matrix n n (R ⧸ I ^ (i + 1)) :=
  (trans I i).mapMatrix

theorem Trans_surjective (i : ℕ) : Function.Surjective (Trans I i (n := n)) := by
  intro M
  refine ⟨M.map (Function.surjInv (trans_surjective I i)), ?_⟩
  ext a b
  simp [Trans, Function.surjInv_eq (trans_surjective I i)]

theorem Trans_sqzero (i : ℕ) (X Y : Matrix n n (R ⧸ I ^ (i + 2))) (hX : Trans I i X = 0)
    (hY : Trans I i Y = 0) : X * Y = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => mul_eq_zero_of_trans I i _ _ ?_ ?_
  · have := congrFun (congrFun hX a) c
    simpa [Trans] using this
  · have := congrFun (congrFun hY c) b
    simpa [Trans] using this

theorem step (hG : IsUnit ((Nat.card G : ℕ) : R)) (i : ℕ) (ρ : G →* GL n (R ⧸ I ^ (i + 1))) :
    ∃ ρ' : G →* GL n (R ⧸ I ^ (i + 2)), (Matrix.GeneralLinearGroup.map (trans I i)).comp ρ' = ρ := by
  have hG' : IsUnit ((Nat.card G : ℕ) : Matrix n n (R ⧸ I ^ (i + 2))) := by
    have := hG.map (algebraMap R (Matrix n n (R ⧸ I ^ (i + 2))))
    simpa only [map_natCast] using this
  obtain ⟨ρ', h⟩ := BrauerLiftSqZero.exists_lift' (π := Trans I i) (Trans_surjective I i)
    (Trans_sqzero I i) hG' ρ
  exact ⟨ρ', h⟩

noncomputable def seq (hG : IsUnit ((Nat.card G : ℕ) : R)) (ρ0 : G →* GL n (R ⧸ I ^ 1)) :
    (i : ℕ) → (G →* GL n (R ⧸ I ^ (i + 1)))
  | 0 => ρ0
  | i + 1 => Classical.choose (step I hG i (seq hG ρ0 i))

theorem seq_zero (hG : IsUnit ((Nat.card G : ℕ) : R)) (ρ0 : G →* GL n (R ⧸ I ^ 1)) :
    seq I hG ρ0 0 = ρ0 := rfl

theorem seq_succ (hG : IsUnit ((Nat.card G : ℕ) : R)) (ρ0 : G →* GL n (R ⧸ I ^ 1)) (i : ℕ) :
    (Matrix.GeneralLinearGroup.map (trans I i)).comp (seq I hG ρ0 (i + 1)) = seq I hG ρ0 i := by
  rw [seq]
  exact Classical.choose_spec (step I hG i (seq I hG ρ0 i))

theorem seq_succ_apply (hG : IsUnit ((Nat.card G : ℕ) : R)) (ρ0 : G →* GL n (R ⧸ I ^ 1)) (i : ℕ)
    (g : G) (a b : n) :
    trans I i ((seq I hG ρ0 (i + 1) g).val a b) = (seq I hG ρ0 i g).val a b := by
  have := congrArg (fun φ : G →* GL n (R ⧸ I ^ (i + 1)) => (φ g).val a b) (seq_succ I hG ρ0 i)
  simpa using this

section limit

theorem smodEq_pow_iff (m : ℕ) (x y : R) :
    x ≡ y [SMOD (I ^ m • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ m := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

variable [IsAdicComplete I R]

theorem eq_zero_of_forall_mem (x : R) (hx : ∀ i : ℕ, x ∈ I ^ (i + 1)) : x = 0 := by
  refine IsHausdorff.haus' (I := I) x fun m => ?_
  rw [smodEq_pow_iff, sub_zero]
  cases m with
  | zero => simp
  | succ i => exact hx i

theorem exists_limit (r : ℕ → R) (hr : ∀ i, Ideal.Quotient.mk (I ^ (i + 1)) (r (i + 1)) =
      Ideal.Quotient.mk (I ^ (i + 1)) (r i)) :
    ∃ L : R, ∀ i, Ideal.Quotient.mk (I ^ (i + 1)) L = Ideal.Quotient.mk (I ^ (i + 1)) (r i) := by

  have hcompat : ∀ i j, i ≤ j → r j - r i ∈ I ^ (i + 1) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j _ ih =>
      have h1 : r (j + 1) - r j ∈ I ^ (i + 1) := by
        have := (Ideal.Quotient.eq (I := I ^ (j + 1))).1 (hr j)
        exact Ideal.pow_le_pow_right (by omega) this
      have : r (j + 1) - r i = (r (j + 1) - r j) + (r j - r i) := by ring
      rw [this]; exact add_mem h1 ih
  let f : ℕ → R := fun m => Nat.casesOn m 0 fun i => r i
  have hf : ∀ {m m'}, m ≤ m' → f m ≡ f m' [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro m m' hmm'
    rw [smodEq_pow_iff]
    cases m with
    | zero => simp
    | succ i =>
      cases m' with
      | zero => omega
      | succ j =>
        have := hcompat i j (by omega)
        rw [← neg_sub]; exact neg_mem this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) f hf
  refine ⟨L, fun i => ?_⟩
  have := (smodEq_pow_iff I (i + 1) _ _).1 (hL (i + 1))

  rw [eq_comm, Ideal.Quotient.eq]
  exact this

theorem exists_lift (hG : IsUnit ((Nat.card G : ℕ) : R)) (ρbar : G →* GL n (R ⧸ I)) :
    ∃ ρ : G →* GL n R, (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp ρ = ρbar := by
  classical
  have h01 : I ≤ I ^ 1 := (pow_one I).ge
  have h10 : I ^ 1 ≤ I := (pow_one I).le
  let ρ0 : G →* GL n (R ⧸ I ^ 1) := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor h01)).comp ρbar
  let sq := seq I hG ρ0

  have hrep : ∀ (g : G) (a b : n) (i : ℕ), ∃ x : R, Ideal.Quotient.mk (I ^ (i + 1)) x = (sq i g).val a b :=
    fun g a b i => Ideal.Quotient.mk_surjective _
  choose r hr using hrep
  have hrcompat : ∀ g a b i, Ideal.Quotient.mk (I ^ (i + 1)) (r g a b (i + 1)) =
      Ideal.Quotient.mk (I ^ (i + 1)) (r g a b i) := by
    intro g a b i
    rw [hr g a b i, ← seq_succ_apply I hG ρ0 i g a b, ← hr g a b (i + 1), trans_mk]
  have hlim : ∀ g a b, ∃ L : R, ∀ i, Ideal.Quotient.mk (I ^ (i + 1)) L = (sq i g).val a b := by
    intro g a b
    obtain ⟨L, hL⟩ := exists_limit I (r g a b) (hrcompat g a b)
    exact ⟨L, fun i => (hL i).trans (hr g a b i)⟩
  choose L hL using hlim
  let M : G → Matrix n n R := fun g => Matrix.of fun a b => L g a b
  have hM : ∀ i g, (M g).map (Ideal.Quotient.mk (I ^ (i + 1))) = (sq i g).val := by
    intro i g; ext a b; simp [M, hL]

  have hvanish : ∀ X : Matrix n n R, (∀ i, X.map (Ideal.Quotient.mk (I ^ (i + 1))) = 0) → X = 0 := by
    intro X hX; ext a b
    refine eq_zero_of_forall_mem I _ fun i => ?_
    have := congrFun (congrFun (hX i) a) b
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this
  have hmul : ∀ g h, M (g * h) = M g * M h := by
    intro g h
    rw [← sub_eq_zero]
    refine hvanish _ fun i => ?_
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, hM, hM, hM, map_mul, Units.val_mul, sub_self]
  have hone : M 1 = 1 := by
    rw [← sub_eq_zero]
    refine hvanish _ fun i => ?_
    rw [Matrix.map_sub _ (map_sub _), hM, map_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), sub_self]
  let U : G → GL n R := fun g =>
    { val := M g
      inv := M g⁻¹
      val_inv := by rw [← hmul, mul_inv_cancel, hone]
      inv_val := by rw [← hmul, inv_mul_cancel, hone] }
  refine ⟨MonoidHom.mk' U fun g h => Units.ext (hmul g h), ?_⟩
  ext g a b
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mk'_apply,
    Matrix.GeneralLinearGroup.map_apply]

  have h0 : Ideal.Quotient.mk (I ^ 1) (M g a b) = Ideal.Quotient.factor h01 ((ρbar g).val a b) := by
    have := congrFun (congrFun (hM 0 g) a) b
    simpa [sq, seq_zero, ρ0] using this
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective ((ρbar g).val a b)
  have := congrArg (Ideal.Quotient.factor h10) h0
  rw [Ideal.Quotient.factor_mk, ← hy, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk] at this
  change Ideal.Quotient.mk I (M g a b) = _
  rw [this, hy]

end limit
p2m_reactivate "P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.BrauerLiftSqZero"

end BrauerLiftComplete
p2m_reactivate "P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.BrauerLiftSqZero"

namespace BrauerLiftEmbed

open Cardinal Polynomial

universe u

section transc

variable {R₀ : Type} [Field R₀]
variable {L : Type} [Field L] [IsAlgClosed L] [Algebra R₀ L]
variable {L' : Type} [Field L'] [IsAlgClosed L'] [Algebra R₀ L']

theorem exists_ringHom_comp_algebraMap (hR₀ : #R₀ ≤ ℵ₀) (hL : ℵ₀ < #L) (hLL' : #L = #L') :
    ∃ f : L →+* L', ∀ r : R₀, f (algebraMap R₀ L r) = algebraMap R₀ L' r := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R₀ L
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R₀ L'
  have hL' : ℵ₀ < #L' := hLL' ▸ hL
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR₀ hL
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR₀ hL'
  have hst : #s = #t := by rw [← h1, ← h2, hLL']
  obtain ⟨e⟩ := Cardinal.eq.1 hst
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e' : Algebra.adjoin R₀ (Set.range ((↑) : s → L)) ≃ₐ[R₀]
      Algebra.adjoin R₀ (Set.range ((↑) : t → L')) :=
    (hs.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv R₀ e)).trans ht.1.aevalEquiv
  let f := IsAlgClosure.equivOfEquiv L L' e'.toRingEquiv
  refine ⟨f.toRingHom, fun r => ?_⟩
  have := IsAlgClosure.equivOfEquiv_algebraMap L L' e'.toRingEquiv
    (algebraMap R₀ (Algebra.adjoin R₀ (Set.range ((↑) : s → L))) r)
  rw [← IsScalarTower.algebraMap_apply] at this
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this]
  change algebraMap _ L' (e' (algebraMap R₀ _ r)) = _
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

end transc
p2m_reactivate "P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.BrauerLiftSqZero"

section witt

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k]

local notation "𝕎" => WittVector p

theorem charZero_witt [Finite k] [CharP k p] : CharZero (𝕎 k) := by
  refine ⟨fun a b hab => ?_⟩

  suffices key : ∀ n : ℕ, ((n : ℕ) : 𝕎 k) = 0 → n = 0 by
    rcases le_total a b with h | h
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
      have : ((c : ℕ) : 𝕎 k) = 0 := by
        have := hab; push_cast at this; linear_combination -this
      have := key c this; omega
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
      have : ((c : ℕ) : 𝕎 k) = 0 := by
        have := hab; push_cast at this; linear_combination this
      have := key c this; omega
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_contra hne
    have hpn : p ∣ n := by
      have h0 := congrArg WittVector.constantCoeff hn
      rw [map_natCast, map_zero] at h0
      exact (CharP.cast_eq_zero_iff k p n).1 h0
    obtain ⟨n', rfl⟩ := hpn
    have hp : 1 < p := (Fact.out : p.Prime).one_lt
    have hn' : n' ≠ 0 := by rintro rfl; simp at hne
    have hlt : n' < p * n' := lt_mul_left (Nat.pos_of_ne_zero hn') hp
    have : ((n' : ℕ) : 𝕎 k) = 0 := by
      apply WittVector.eq_zero_of_p_mul_eq_zero
      rw [mul_comm]; exact_mod_cast hn
    exact hn' (ih n' hlt this)

theorem teichmuller_injective : Function.Injective (WittVector.teichmuller p : k → 𝕎 k) := by
  intro a b h
  have := congrArg (fun w : 𝕎 k => w.coeff 0) h
  simpa [WittVector.teichmuller_coeff_zero] using this

omit [Fact p.Prime] in
theorem mk_witt [Finite k] : #(𝕎 k) = 𝔠 := by
  have e : 𝕎 k ≃ (ℕ → k) :=
    { toFun := fun w => w.coeff
      invFun := fun f => WittVector.mk p f
      left_inv := fun w => by ext i; rfl
      right_inv := fun f => by rfl }
  haveI := Fintype.ofFinite k
  rw [Cardinal.mk_congr e]
  simp only [mk_pi, prod_const, mk_fintype, lift_natCast, lift_aleph0, Cardinal.mk_eq_aleph0]
  exact nat_power_aleph0 Fintype.one_lt_card

theorem exists_embedding [Finite k] [CharP k p] (m : ℕ) (hm : 0 < m) (x : k) (hx : IsPrimitiveRoot x m) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ m) :
    ∃ ι : 𝕎 k →+* ℂ, Function.Injective ι ∧ ι (WittVector.teichmuller p x) = ζ := by
  haveI : CharZero (𝕎 k) := charZero_witt p k
  let K := FractionRing (𝕎 k)
  let L := AlgebraicClosure K
  have hinjKL : Function.Injective (algebraMap (𝕎 k) L) := by
    rw [IsScalarTower.algebraMap_eq (𝕎 k) K L, RingHom.coe_comp]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective (𝕎 k) K)
  haveI : CharZero L := charZero_of_injective_algebraMap hinjKL

  set μ : L := algebraMap (𝕎 k) L (WittVector.teichmuller p x) with hμdef
  have hμ : IsPrimitiveRoot μ m :=
    (hx.map_of_injective (teichmuller_injective p k)).map_of_injective hinjKL

  haveI : Fact (Irreducible (cyclotomic m ℚ)) := ⟨cyclotomic.irreducible_rat hm⟩
  let R₀ := AdjoinRoot (cyclotomic m ℚ)
  have hrootL : (cyclotomic m ℚ).eval₂ (algebraMap ℚ L) μ = 0 := by
    rw [eval₂_eq_eval_map, map_cyclotomic]; exact hμ.isRoot_cyclotomic hm
  have hrootC : (cyclotomic m ℚ).eval₂ (algebraMap ℚ ℂ) ζ = 0 := by
    rw [eval₂_eq_eval_map, map_cyclotomic]; exact hζ.isRoot_cyclotomic hm
  let jL : R₀ →+* L := AdjoinRoot.lift (algebraMap ℚ L) μ hrootL
  let jC : R₀ →+* ℂ := AdjoinRoot.lift (algebraMap ℚ ℂ) ζ hrootC
  letI algL : Algebra R₀ L := jL.toAlgebra
  letI algC : Algebra R₀ ℂ := jC.toAlgebra

  have hR₀ : #R₀ ≤ ℵ₀ := by
    calc #R₀ ≤ #ℚ[X] := mk_le_of_surjective AdjoinRoot.mk_surjective
      _ ≤ max #ℚ ℵ₀ := Polynomial.cardinalMk_le_max
      _ = ℵ₀ := by rw [Cardinal.mkRat, max_self]
  have hK : #K = 𝔠 := by
    change #(Localization (nonZeroDivisors (𝕎 k))) = 𝔠
    rw [Localization.cardinalMk le_rfl, mk_witt]
  have hLcard : #L = 𝔠 := by
    apply le_antisymm
    · calc #L ≤ max #K ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max K L
        _ = 𝔠 := by rw [hK, max_eq_left aleph0_le_continuum]
    · rw [← mk_witt p k]; exact mk_le_of_injective hinjKL
  have hLℂ : #L = #ℂ := by rw [hLcard, Cardinal.mk_complex]
  have hL : ℵ₀ < #L := by rw [hLcard]; exact aleph0_lt_continuum
  obtain ⟨f, hf⟩ := exists_ringHom_comp_algebraMap (R₀ := R₀) (L := L) (L' := ℂ) hR₀ hL hLℂ
  refine ⟨f.comp (algebraMap (𝕎 k) L), f.injective.comp hinjKL, ?_⟩
  have h1 : algebraMap R₀ L (AdjoinRoot.root _) = μ := AdjoinRoot.lift_root hrootL
  have h2 : algebraMap R₀ ℂ (AdjoinRoot.root _) = ζ := AdjoinRoot.lift_root hrootC
  rw [RingHom.comp_apply, ← hμdef, ← h1, hf, h2]

end witt
p2m_reactivate "P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.BrauerLiftSqZero"

end BrauerLiftEmbed
p2m_reactivate "P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.BrauerLiftSqZero"

namespace BrauerLiftMain

open Polynomial Matrix

theorem map_prod_X_sub_C_pow {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (s : Multiset ℂ) (a : A) (e : ℂ → ℕ) :
    ((s.map fun r => X - C (a ^ e r)).prod).map f = (s.map fun r => X - C (f a ^ e r)).prod := by
  rw [Polynomial.map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  simp [Polynomial.map_sub, map_pow]

theorem pow_eq_one_of_mem_roots_charpoly {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ}
    (A : Matrix n n ℂ) (hA : A ^ m = 1) {r : ℂ} (hr : r ∈ A.charpoly.roots) : r ^ m = 1 := by
  have hroot : IsRoot A.charpoly r := (mem_roots (charpoly_monic A).ne_zero).1 hr
  have hspec : r ∈ spectrum ℂ A := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have hpow := spectrum.pow_mem_pow A m hspec
  rw [hA, spectrum.mem_iff] at hpow
  by_contra hne
  apply hpow
  have : (algebraMap ℂ (Matrix n n ℂ) (r ^ m) - 1) = algebraMap ℂ (Matrix n n ℂ) (r ^ m - 1) := by
    rw [map_sub, map_one]
  rw [this]
  exact (isUnit_iff_ne_zero.2 (sub_ne_zero.2 hne)).map _

section main

theorem main (G : Type) [Group G] [Finite G]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ Nat.card G)
    (k : Type) [Field k] [Finite k] [CharP k ℓ]
    (n m : ℕ) (hm : 0 < m) (hℓm : ¬ ℓ ∣ m) (hGm : ∀ g : G, g ^ m = 1)
    (S : Subalgebra ℤ ℂ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (hζS : ζ ∈ S) (φ : S →+* k)
    (ρbar : G →* GL (Fin n) k) :
    ∃ ρ : G →* GL (Fin n) ℂ, ∀ g : G, ∃ P : Polynomial S,
      P.map (algebraMap S ℂ) = ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly ∧
      P.map φ = ((ρbar g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩

  set zS : S := ⟨ζ, hζS⟩ with hzSdef
  set x : k := φ zS with hxdef
  have hzS : IsPrimitiveRoot zS m :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap S ℂ)
      (show IsPrimitiveRoot (algebraMap S ℂ zS) m from hζ) Subtype.val_injective
  have hx : IsPrimitiveRoot x m := by
    haveI : NeZero (m : k) := ⟨by
      intro h; exact hℓm ((CharP.cast_eq_zero_iff k ℓ m).1 h)⟩
    have h1 : (cyclotomic m S).eval zS = 0 := by
      have h2 : (cyclotomic m ℂ).eval ζ = 0 := hζ.isRoot_cyclotomic hm
      rw [← map_cyclotomic m (algebraMap S ℂ), eval_map] at h2
      change eval₂ (algebraMap S ℂ) (algebraMap S ℂ zS) (cyclotomic m S) = 0 at h2
      rw [eval₂_hom] at h2
      exact (map_eq_zero_iff _ Subtype.val_injective).1 h2
    have h3 : (cyclotomic m k).eval x = 0 := by
      rw [← map_cyclotomic m φ, eval_map, eval₂_hom, h1, map_zero]
    exact isRoot_cyclotomic_iff.1 h3

  obtain ⟨ι, hι, hιτ⟩ := BrauerLiftEmbed.exists_embedding ℓ k m hm x hx ζ hζ

  let I : Ideal (WittVector ℓ k) := Ideal.span {(ℓ : WittVector ℓ k)}
  have hGunit : IsUnit ((Nat.card G : ℕ) : WittVector ℓ k) := by
    have hk : ((Nat.card G : ℕ) : k) ≠ 0 := fun h => hℓ ((CharP.cast_eq_zero_iff k ℓ _).1 h)
    obtain ⟨y, hy⟩ := WittVector.constantCoeff_surjective (p := ℓ) ((Nat.card G : ℕ) : k)⁻¹
    have hmem : ((Nat.card G : ℕ) : WittVector ℓ k) * y - 1 ∈ I := by
      change _ ∈ Ideal.span _
      rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_natCast, hy, map_one,
        mul_inv_cancel₀ hk, sub_self]
    have hjac := IsAdicComplete.le_jacobson_bot I hmem
    rw [Ideal.mem_jacobson_bot] at hjac
    have := hjac 1
    rw [mul_one, sub_add_cancel] at this
    exact isUnit_of_mul_isUnit_left this
  let qe : WittVector ℓ k ⧸ I ≃+* k := WittVector.quotientPEquiv
  let ρbar' : G →* GL (Fin n) (WittVector ℓ k ⧸ I) :=
    (Matrix.GeneralLinearGroup.map qe.symm.toRingHom).comp ρbar
  obtain ⟨ρW, hρW⟩ := BrauerLiftComplete.exists_lift I hGunit ρbar'
  have hred : ∀ g, ((ρW g).val).map WittVector.constantCoeff = (ρbar g).val := by
    intro g
    have h1 := congrArg (fun ψ : G →* GL (Fin n) (WittVector ℓ k ⧸ I) => (ψ g).val) hρW
    simp only [MonoidHom.coe_comp, Function.comp_apply, Matrix.GeneralLinearGroup.val_map_apply,
      ρbar'] at h1
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) (WittVector ℓ k ⧸ I) => M.map qe) h1
    simp only [Matrix.map_map, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h2
    have hqe : (qe : WittVector ℓ k ⧸ I → k) ∘ (Ideal.Quotient.mk I) = WittVector.constantCoeff := by
      funext w; rfl
    have hqe' : (qe : WittVector ℓ k ⧸ I → k) ∘ (qe.symm : k → WittVector ℓ k ⧸ I) = id := by
      funext w; simp
    rw [hqe, hqe', Matrix.map_id] at h2
    exact h2

  refine ⟨(Matrix.GeneralLinearGroup.map ι).comp ρW, fun g => ?_⟩
  set A : Matrix (Fin n) (Fin n) (WittVector ℓ k) := (ρW g).val with hAdef
  have hAC : (((Matrix.GeneralLinearGroup.map ι).comp ρW g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      = A.map ι := by
    simp [hAdef]
  rw [hAC]
  have hpow : (A.map ι) ^ m = 1 := by
    have : ((Matrix.GeneralLinearGroup.map ι).comp ρW g) ^ m = 1 := by rw [← map_pow, hGm, map_one]
    have := congrArg (fun u : GL (Fin n) ℂ => (u : Matrix (Fin n) (Fin n) ℂ)) this
    simpa [Units.val_pow_eq_pow_val] using this

  set rts := (A.map ι).charpoly.roots with hrts
  have hexp : ∀ r ∈ rts, ∃ i : ℕ, ζ ^ i = r := fun r hr => by
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (pow_eq_one_of_mem_roots_charpoly _ hpow hr)
    exact ⟨i, hi⟩
  let e : ℂ → ℕ := fun r => if h : ∃ i : ℕ, ζ ^ i = r then h.choose else 0
  have he : ∀ r ∈ rts, ζ ^ e r = r := fun r hr => by
    simp only [e, dif_pos (hexp r hr)]
    exact (hexp r hr).choose_spec
  have hsplit : (A.map ι).charpoly = (rts.map fun r => X - C r).prod :=
    (IsAlgClosed.splits _).eq_prod_roots_of_monic (charpoly_monic _)

  refine ⟨(rts.map fun r => X - C (zS ^ e r)).prod, ?_, ?_⟩
  · rw [map_prod_X_sub_C_pow, hsplit]
    congr 1
    refine Multiset.map_congr rfl fun r hr => ?_
    change X - C ((ζ : ℂ) ^ e r) = _
    rw [he r hr]
  ·
    have hQ : (rts.map fun r => X - C (WittVector.teichmuller ℓ x ^ e r)).prod = A.charpoly := by
      apply Polynomial.map_injective ι hι
      rw [map_prod_X_sub_C_pow, hιτ, ← Matrix.charpoly_map, hsplit]
      congr 1
      exact Multiset.map_congr rfl fun r hr => by rw [he r hr]
    have h1 : ((rts.map fun r => X - C (zS ^ e r)).prod).map φ
        = (rts.map fun r => X - C (x ^ e r)).prod := by
      rw [map_prod_X_sub_C_pow]
    have h2 : A.charpoly.map WittVector.constantCoeff = (rts.map fun r => X - C (x ^ e r)).prod := by
      rw [← hQ, map_prod_X_sub_C_pow]
      simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [h1, ← h2, ← Matrix.charpoly_map, hred]

end main
p2m_reactivate "P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.BrauerLiftSqZero"

end BrauerLiftMain
p2m_reactivate "P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.BrauerLiftSqZero"

open Polynomial
open scoped MatrixGroups

theorem solution
    (G : Type) [Group G] [Finite G]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ Nat.card G)
    (k : Type) [Field k] [Finite k] [CharP k ℓ]
    (n m : ℕ) (hm : 0 < m) (hℓm : ¬ ℓ ∣ m) (hGm : ∀ g : G, g ^ m = 1)
    (S : Subalgebra ℤ ℂ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (hζS : ζ ∈ S) (φ : S →+* k)
    (ρbar : G →* GL (Fin n) k) :
    ∃ ρ : G →* GL (Fin n) ℂ, ∀ g : G, ∃ P : Polynomial S,
      P.map (algebraMap S ℂ) = ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly ∧
      P.map φ = ((ρbar g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly :=
  BrauerLiftMain.main G ℓ hℓ k n m hm hℓm hGm S ζ hζ hζS φ ρbar

end S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard
end P2MW
export P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard (solution)
