-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.concaveClosure_eq_of_exc
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:19:30.210955+00:00
-- url     : https://prove2.me/submissions/1a415219-415d-43b9-9bd9-a94c3a1e7e86

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization

set_option autoImplicit false

namespace Sol2f8a2c6e

open SteinitzExchange.LocalSupermod

/-! ## S1.0 Linear algebra of `pairing` and `toReal` -/

theorem murota_pairing_add_right {V : Type*} [Fintype V] (p b c : V → ℝ) :
    pairing p (b + c) = pairing p b + pairing p c := by
  simp only [pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem murota_pairing_smul_right {V : Type*} [Fintype V] (p b : V → ℝ) (a : ℝ) :
    pairing p (a • b) = a * pairing p b := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

theorem murota_pairing_smul_left {V : Type*} [Fintype V] (p b : V → ℝ) (a : ℝ) :
    pairing (a • p) b = a * pairing p b := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

theorem murota_pairing_add_left {V : Type*} [Fintype V] (p q b : V → ℝ) :
    pairing (p + q) b = pairing p b + pairing q b := by
  simp only [pairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem murota_pairing_sub_left {V : Type*} [Fintype V] (p q b : V → ℝ) :
    pairing (p - q) b = pairing p b - pairing q b := by
  simp only [pairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem murota_pairing_zero_left {V : Type*} [Fintype V] (b : V → ℝ) :
    pairing 0 b = 0 := by
  simp only [pairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-! ## S1.1 The concave conjugate and the closure family -/

theorem murota_concaveConj_le {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) (p : V → ℝ) {x : V → ℤ} (hx : x ∈ B) :
    concaveConj B g p ≤ pairing p (toReal x) - g x := by
  unfold concaveConj
  have : Finite (B : Set (V → ℤ)) := B.finite_toSet.to_subtype
  have hbdd : BddBelow (Set.range fun y : (B : Set (V → ℤ)) =>
      pairing p (toReal (y : V → ℤ)) - g y) := (Set.finite_range _).bddBelow
  exact ciInf_le hbdd (⟨x, hx⟩ : (B : Set (V → ℤ)))

theorem murota_exists_concaveConj_eq {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (p : V → ℝ) :
    ∃ x ∈ B, concaveConj B g p = pairing p (toReal x) - g x := by
  unfold concaveConj
  have : Finite (B : Set (V → ℤ)) := B.finite_toSet.to_subtype
  have : Nonempty (B : Set (V → ℤ)) := by
    obtain ⟨x, hx⟩ := hB
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨⟨x, hx⟩, hxe⟩ := exists_eq_ciInf_of_finite
    (f := fun y : (B : Set (V → ℤ)) => pairing p (toReal (y : V → ℤ)) - g y)
  exact ⟨x, hx, hxe.symm⟩

/-- Every member of the closure family is `≥ c` on `B̄` when `c ≤ g` on `B`. -/
theorem murota_family_ge_of_le {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) (c : ℝ) (hc : ∀ x ∈ B, c ≤ g x) (p : V → ℝ) {b : V → ℝ}
    (hb : b ∈ hull B) : c ≤ pairing p b - concaveConj B g p := by
  set k := concaveConj B g p with hk
  have hsub : toReal '' (B : Set (V → ℤ)) ⊆ {b | c ≤ pairing p b - k} := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := murota_concaveConj_le B g p (Finset.mem_coe.mp hx)
    have h2 := hc x (Finset.mem_coe.mp hx)
    show c ≤ pairing p (toReal x) - k
    linarith
  have hconv : Convex ℝ {b | c ≤ pairing p b - k} := by
    intro x hx y hy a t ha ht hat
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [murota_pairing_add_right, murota_pairing_smul_right, murota_pairing_smul_right]
    have e1 : a * c + t * c = c := by rw [← add_mul, hat, one_mul]
    have e2 : a * k + t * k = k := by rw [← add_mul, hat, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy ht]
  exact convexHull_min hsub hconv hb

theorem murota_bddBelow_family {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (hB : B.Nonempty) (g : (V → ℤ) → ℝ) {b : V → ℝ} (hb : b ∈ hull B) :
    BddBelow (Set.range fun p : V → ℝ => pairing p b - concaveConj B g p) := by
  obtain ⟨x0, hx0, hmin⟩ := B.exists_min_image g hB
  refine ⟨g x0, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact murota_family_ge_of_le B g (g x0) hmin p hb

theorem murota_concaveClosure_le {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (hB : B.Nonempty) (g : (V → ℤ) → ℝ) {b : V → ℝ} (hb : b ∈ hull B) (p : V → ℝ) :
    concaveClosure B g b ≤ pairing p b - concaveConj B g p :=
  ciInf_le (murota_bddBelow_family B hB g hb) p

/-! ## S1.3 Deliverable (b): the closure majorises `g` on `B`; and `ĝ ≤ max g` on `B̄` -/

theorem murota_le_concaveClosure {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) {x : V → ℤ} (hx : x ∈ B) :
    g x ≤ concaveClosure B g (toReal x) := by
  unfold concaveClosure
  refine le_ciInf fun p => ?_
  have := murota_concaveConj_le B g p hx
  linarith

theorem murota_concaveClosure_le_of_le {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (M : ℝ) (hM : ∀ x ∈ B, g x ≤ M)
    {b : V → ℝ} (hb : b ∈ hull B) : concaveClosure B g b ≤ M := by
  have h := murota_concaveClosure_le B hB g hb 0
  obtain ⟨x, hx, hxe⟩ := murota_exists_concaveConj_eq B hB g 0
  rw [hxe, murota_pairing_zero_left, murota_pairing_zero_left] at h
  have := hM x hx
  linarith

/-! ## S1.4 Deliverable (c): under (EXC), `argmax(ω[p])` is an integral base set -/

theorem murota_perturb_exchange_sum {V : Type*} [Fintype V] [DecidableEq V]
    (ω : (V → ℤ) → ℝ) (p : V → ℝ) (x y : V → ℤ) (u v : V) :
    perturb ω p (x - chi u + chi v) + perturb ω p (y + chi u - chi v) =
      ω (x - chi u + chi v) + ω (y + chi u - chi v) + (pairing p (toReal x) + pairing p (toReal y)) := by
  unfold perturb
  have : pairing p (toReal (x - chi u + chi v)) + pairing p (toReal (y + chi u - chi v)) =
      pairing p (toReal x) + pairing p (toReal y) := by
    rw [← murota_pairing_add_right, ← murota_pairing_add_right]
    congr 1
    funext w
    simp only [toReal, Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub]
    ring
  linarith

/-! ## S1.6 Deliverable (e): potentials for a digraph with no positive cycle

A walk is a vertex list `L` with `L.IsChain adj`; its weight is `murotaWalkWeight w L`
(sum of `w a b` over consecutive pairs). A closed walk is one with `L.head? = L.getLast?`. -/

/-- Weight of a walk given by its vertex list. -/
def murotaWalkWeight {V : Type*} (w : V → V → ℝ) : List V → ℝ
  | a :: b :: l => w a b + murotaWalkWeight w (b :: l)
  | _ => 0

theorem murotaWalkWeight_nil {V : Type*} (w : V → V → ℝ) : murotaWalkWeight w [] = 0 := rfl

theorem murotaWalkWeight_single {V : Type*} (w : V → V → ℝ) (a : V) :
    murotaWalkWeight w [a] = 0 := rfl

theorem murotaWalkWeight_cons_cons {V : Type*} (w : V → V → ℝ) (a b : V) (l : List V) :
    murotaWalkWeight w (a :: b :: l) = w a b + murotaWalkWeight w (b :: l) := rfl

theorem murotaWalkWeight_append {V : Type*} (w : V → V → ℝ) (x : V) (l₂ : List V) :
    ∀ l₁ : List V, murotaWalkWeight w (l₁ ++ x :: l₂) =
      murotaWalkWeight w (l₁ ++ [x]) + murotaWalkWeight w (x :: l₂)
  | [] => by simp [murotaWalkWeight_single]
  | [a] => by simp [murotaWalkWeight_cons_cons, murotaWalkWeight_single]
  | a :: b :: l₁ => by
    have ih := murotaWalkWeight_append w x l₂ (b :: l₁)
    simp only [List.cons_append] at ih ⊢
    rw [murotaWalkWeight_cons_cons, murotaWalkWeight_cons_cons, ih]
    ring

theorem murotaWalkWeight_le {V : Type*} (w : V → V → ℝ) (K : ℝ) (hK : ∀ a b, w a b ≤ K)
    (hK0 : 0 ≤ K) : ∀ l : List V, murotaWalkWeight w l ≤ l.length * K
  | [] => by simp [murotaWalkWeight_nil]
  | [a] => by simp [murotaWalkWeight_single]; exact hK0
  | a :: b :: l => by
    have ih := murotaWalkWeight_le w K hK hK0 (b :: l)
    rw [murotaWalkWeight_cons_cons]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at ih ⊢
    linarith [hK a b]

theorem murota_exists_split_of_not_nodup {V : Type*} {x : V} :
    ∀ L : List V, [x, x].Sublist L → ∃ a b c : List V, L = a ++ x :: (b ++ x :: c)
  | [], h => by simp at h
  | y :: L, h => by
    rcases List.sublist_cons_iff.mp h with h' | ⟨r, hr, h'⟩
    · obtain ⟨a, b, c, rfl⟩ := murota_exists_split_of_not_nodup L h'
      exact ⟨y :: a, b, c, by simp⟩
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨b, c, rfl⟩ := List.append_of_mem (List.singleton_sublist.mp h')
      exact ⟨[], b, c, by simp⟩

/-- Cycle removal: every walk is dominated by a simple walk with the same last vertex. -/
theorem murota_exists_nodup_walk {V : Type*} (adj : V → V → Prop) (w : V → V → ℝ)
    (hcyc : ∀ L : List V, L.IsChain adj → L.head? = L.getLast? → murotaWalkWeight w L ≤ 0) :
    ∀ n : ℕ, ∀ L : List V, L.length ≤ n → L.IsChain adj →
      ∃ L' : List V, L'.IsChain adj ∧ L'.getLast? = L.getLast? ∧ L'.Nodup ∧
        murotaWalkWeight w L ≤ murotaWalkWeight w L' := by
  intro n
  induction n with
  | zero =>
    intro L hL hc
    have : L = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hL)
    subst this
    exact ⟨[], hc, rfl, List.nodup_nil, le_rfl⟩
  | succ n ih =>
    intro L hL hc
    by_cases hnd : L.Nodup
    · exact ⟨L, hc, rfl, hnd, le_rfl⟩
    rw [List.nodup_iff_sublist] at hnd
    simp only [not_forall, not_not] at hnd
    obtain ⟨x, hx⟩ := hnd
    obtain ⟨a, b, c, rfl⟩ := murota_exists_split_of_not_nodup _ hx
    -- the shortcut walk
    have hc' := hc
    rw [List.isChain_append] at hc'
    obtain ⟨hca, hcx, hlink⟩ := hc'
    have hcxc : (x :: c).IsChain adj := hcx.suffix ⟨x :: b, by simp⟩
    have hcyc_chain : (x :: (b ++ [x])).IsChain adj := hcx.infix ⟨[], c, by simp⟩
    have hshort : (a ++ x :: c).IsChain adj :=
      List.isChain_append.mpr ⟨hca, hcxc, by simpa using hlink⟩
    have hlen : (a ++ x :: c).length ≤ n := by
      simp only [List.length_append, List.length_cons] at hL ⊢
      omega
    obtain ⟨L', hL'c, hL'last, hL'nd, hL'w⟩ := ih _ hlen hshort
    have hlast : (x :: (b ++ x :: c)).getLast? = (x :: c).getLast? := by
      rw [List.getLast?_cons, List.getLast?_append, List.getLast?_cons]
      rfl
    refine ⟨L', hL'c, ?_, hL'nd, ?_⟩
    · rw [hL'last, List.getLast?_append, List.getLast?_append, hlast]
    · have hcycw := hcyc _ hcyc_chain (by rw [← List.cons_append, List.getLast?_concat]; rfl)
      have e1 := murotaWalkWeight_append w x (b ++ x :: c) a
      have e2 := murotaWalkWeight_append w x c (x :: b)
      have e3 := murotaWalkWeight_append w x c a
      simp only [List.cons_append] at e2
      linarith

theorem murota_exists_potential {V : Type*} [Fintype V] (adj : V → V → Prop) (w : V → V → ℝ)
    (hcyc : ∀ L : List V, L.IsChain adj → L.head? = L.getLast? → murotaWalkWeight w L ≤ 0) :
    ∃ p : V → ℝ, ∀ u v, adj u v → w u v ≤ p v - p u := by
  classical
  set K : ℝ := ∑ a, ∑ b, |w a b| with hKdef
  have hK : ∀ a b, w a b ≤ K := by
    intro a b
    refine (le_abs_self _).trans ?_
    calc |w a b| ≤ ∑ b', |w a b'| :=
          Finset.single_le_sum (f := fun b' => |w a b'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
      _ ≤ K := Finset.single_le_sum (f := fun a' => ∑ b', |w a' b'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  let S : V → Set ℝ := fun v =>
    {r | ∃ L : List V, L.IsChain adj ∧ L.getLast? = some v ∧ murotaWalkWeight w L = r}
  have hne : ∀ v, (S v).Nonempty := fun v => ⟨0, [v], List.isChain_singleton v, rfl, rfl⟩
  have hbdd : ∀ v, BddAbove (S v) := by
    intro v
    refine ⟨(Fintype.card V : ℝ) * K, ?_⟩
    rintro _ ⟨L, hLc, _, rfl⟩
    obtain ⟨L', _, _, hnd, hle⟩ := murota_exists_nodup_walk adj w hcyc L.length L le_rfl hLc
    have h1 := murotaWalkWeight_le w K hK hK0 L'
    have h2 : (L'.length : ℝ) ≤ Fintype.card V := by exact_mod_cast hnd.length_le_card
    nlinarith
  refine ⟨fun v => sSup (S v), fun u v huv => ?_⟩
  have key : sSup (S u) ≤ sSup (S v) - w u v := by
    refine csSup_le (hne u) ?_
    rintro _ ⟨L, hLc, hLl, rfl⟩
    obtain ⟨L0, rfl⟩ := List.getLast?_eq_some_iff.mp hLl
    have hmem : murotaWalkWeight w ((L0 ++ [u]) ++ [v]) ∈ S v := by
      refine ⟨(L0 ++ [u]) ++ [v], ?_, by simp, rfl⟩
      exact List.isChain_append.mpr ⟨hLc, List.isChain_singleton v, by simpa using huv⟩
    have hw : murotaWalkWeight w ((L0 ++ [u]) ++ [v]) = murotaWalkWeight w (L0 ++ [u]) + w u v := by
      rw [List.append_assoc, List.singleton_append, murotaWalkWeight_append w u [v] L0,
        murotaWalkWeight_cons_cons, murotaWalkWeight_single]
      ring
    have := le_csSup (hbdd v) hmem
    linarith
  show w u v ≤ sSup (S v) - sSup (S u)
  linarith

/-! ## S2 Lemma 4.5: under (EXC) there is a supergradient at every point of `B`

Route (Murota 1996, Lemma 4.5):
1. `murota_local_opt`: local optimality by induction on the l1 distance.
2. `murota_exc_triangle`: in the exchange graph at `x` (arcs `u → v` when `x − χ_u + χ_v ∈ B`,
   weight `ω(x − χ_u + χ_v) − ω x`) two consecutive arcs can be shortcut, weight not decreasing.
3. `murota_exc_no_positive_cycle`: hence every closed walk has weight `≤ 0`.
4. `murota_exists_potential` (S1) gives potentials; local optimality of `ω[−p]` at `x`
   gives the supergradient `murota_exists_supergradient`. -/

/-! ### S2.0 Linear algebra of `toReal`, `chi` and `pairing` -/

theorem murota_pairing_sub_right {V : Type*} [Fintype V] (p b c : V → ℝ) :
    pairing p (b - c) = pairing p b - pairing p c := by
  simp only [pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem murota_pairing_neg_left {V : Type*} [Fintype V] (p b : V → ℝ) :
    pairing (-p) b = -pairing p b := by
  simp only [pairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem murota_toReal_add {V : Type*} (a b : V → ℤ) : toReal (a + b) = toReal a + toReal b := by
  funext w
  simp only [toReal, Pi.add_apply, Int.cast_add]

theorem murota_toReal_sub {V : Type*} (a b : V → ℤ) : toReal (a - b) = toReal a - toReal b := by
  funext w
  simp only [toReal, Pi.sub_apply, Int.cast_sub]

theorem murota_pairing_toReal_chi {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (u : V) :
    pairing p (toReal (chi u)) = p u := by
  unfold pairing
  rw [Finset.sum_eq_single u]
  · simp [toReal, chi]
  · intro b _ hb
    simp [toReal, chi, hb]
  · intro h
    exact absurd (Finset.mem_univ u) h

/-- `⟨p, x − χ_u + χ_v⟩ = ⟨p, x⟩ − p u + p v`. -/
theorem murota_pairing_toReal_exchange {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ)
    (x : V → ℤ) (u v : V) :
    pairing p (toReal (x - chi u + chi v)) = pairing p (toReal x) - p u + p v := by
  rw [murota_toReal_add, murota_toReal_sub, murota_pairing_add_right, murota_pairing_sub_right,
    murota_pairing_toReal_chi, murota_pairing_toReal_chi]

/-! ### S2.1 (EXC) is preserved by linear perturbation -/

theorem murota_perturb_satisfiesEXC {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) (p : V → ℝ) :
    SatisfiesEXC B (perturb ω p) := by
  intro x hx y hy u hu
  obtain ⟨v, hv, h1, h2, hle⟩ := hω x hx y hy u hu
  refine ⟨v, hv, h1, h2, ?_⟩
  have key := murota_perturb_exchange_sum ω p x y u v
  have e : perturb ω p x + perturb ω p y =
      ω x + ω y + (pairing p (toReal x) + pairing p (toReal y)) := by
    unfold perturb
    ring
  linarith

/-! ### S2.2 Local optimality (induction on the l1 distance) -/

/-- Under (EXC), two distinct points of `B` have `supp⁺(x − y) ≠ ∅`. -/
theorem murota_exists_pos_of_ne {V : Type*} [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (hne : y ≠ x) : ∃ u : V, 0 < (x - y) u := by
  by_contra h
  simp only [not_exists, not_lt] at h
  obtain ⟨u, hu⟩ := Function.ne_iff.mp hne
  have h1 : 0 < (y - x) u := by
    have := h u
    simp only [Pi.sub_apply] at this ⊢
    omega
  obtain ⟨v, hv, -⟩ := hω y hy x hx u h1
  have := h v
  simp only [Pi.sub_apply] at this hv
  omega

/-- The exchange `y ↦ y + χ_u − χ_v` with `u ∈ supp⁺(x − y)`, `v ∈ supp⁻(x − y)` moves `y`
strictly closer to `x` in the l1 distance. -/
theorem murota_l1_exchange_lt {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) (u v : V)
    (hu : 0 < (x - y) u) (hv : (x - y) v < 0) :
    ∑ w, (x w - (y + chi u - chi v) w).natAbs < ∑ w, (x w - y w).natAbs := by
  simp only [Pi.sub_apply] at hu hv
  have huv : u ≠ v := by
    rintro rfl
    omega
  apply Finset.sum_lt_sum
  · intro w _
    simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply]
    split_ifs with h1 h2 h2 <;> subst_vars <;> omega
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    have e : (y + chi u - chi v) u = y u + 1 := by simp [chi, huv]
    rw [e]
    omega

/-- Local optimality (Murota 1996, Theorem 2.? / Lemma 4.5 step 1): under (EXC), a point of `B`
that is not improved by any single exchange `x − χ_u + χ_v` is a global maximiser on `B`. -/
theorem murota_local_opt {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B)
    (hloc : ∀ u v : V, x - chi u + chi v ∈ B → ω (x - chi u + chi v) ≤ ω x) :
    ∀ y ∈ B, ω y ≤ ω x := by
  suffices H : ∀ n : ℕ, ∀ y ∈ B, ∑ w, (x w - y w).natAbs < n → ω y ≤ ω x from
    fun y hy => H _ y hy (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro y _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro y hy hn
    by_cases hyx : y = x
    · rw [hyx]
    obtain ⟨u, hu⟩ := murota_exists_pos_of_ne B ω hω hx hy hyx
    obtain ⟨v, hv, hx', hy', hle⟩ := hω x hx y hy u hu
    have h1 := hloc u v hx'
    have hlt := murota_l1_exchange_lt x y u v hu hv
    have h2 := ih (y + chi u - chi v) hy' (by omega)
    linarith

/-! ### S2.3 The exchange graph at `x` has no positive cycle -/

/-- Shortcut of two consecutive arcs `a → b → c` of the exchange graph at `x`. -/
theorem murota_exc_triangle {V : Type*} [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (a b c : V)
    (hab : x - chi a + chi b ∈ B) (hbc : x - chi b + chi c ∈ B) :
    x - chi a + chi c ∈ B ∧
      ω (x - chi a + chi b) + ω (x - chi b + chi c) ≤ ω x + ω (x - chi a + chi c) := by
  by_cases hba : b = a
  · subst hba
    simp only [sub_add_cancel]
    exact ⟨hbc, le_refl _⟩
  by_cases hbc' : b = c
  · subst hbc'
    simp only [sub_add_cancel]
    exact ⟨hab, by linarith⟩
  have hpos : 0 < (x - chi a + chi b - (x - chi b + chi c)) b := by
    have e : (x - chi a + chi b - (x - chi b + chi c)) b = 2 := by simp [chi, hba, hbc']
    omega
  obtain ⟨v, hv, hm1, hm2, hle⟩ := hω _ hab _ hbc b hpos
  have hv' : v = a ∨ v = c := by
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hva, hvc⟩ := hcon
    simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply, if_neg hva, if_neg hvc] at hv
    split_ifs at hv <;> omega
  rcases hv' with h | h
  · rw [h] at hm1 hm2 hle
    have e1 : x - chi a + chi b - chi b + chi a = x := by abel
    have e2 : x - chi b + chi c + chi b - chi a = x - chi a + chi c := by abel
    rw [e1, e2] at hle
    rw [e2] at hm2
    exact ⟨hm2, hle⟩
  · rw [h] at hm1 hm2 hle
    have e1 : x - chi a + chi b - chi b + chi c = x - chi a + chi c := by abel
    have e2 : x - chi b + chi c + chi b - chi c = x := by abel
    rw [e1, e2] at hle
    rw [e1] at hm1
    exact ⟨hm1, by linarith⟩

/-- A walk `a → ⋯ → b` in the exchange graph at `x` is dominated by the single arc `a → b`. -/
theorem murota_exc_walk_le {V : Type*} [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B) :
    ∀ (L : List V) (a b : V), (a :: L).IsChain (fun u v => x - chi u + chi v ∈ B) →
      (a :: L).getLast? = some b →
      x - chi a + chi b ∈ B ∧
        murotaWalkWeight (fun u v => ω (x - chi u + chi v) - ω x) (a :: L) ≤
          ω (x - chi a + chi b) - ω x
  | [], a, b, _, hl => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl
    rw [murotaWalkWeight_single, sub_add_cancel]
    exact ⟨hx, le_of_eq (sub_self _).symm⟩
  | c :: L, a, b, hc, hl => by
    rw [List.isChain_cons_cons] at hc
    rw [List.getLast?_cons_cons] at hl
    obtain ⟨h1, h2⟩ := murota_exc_walk_le B ω hω hx L c b hc.2 hl
    obtain ⟨h3, h4⟩ := murota_exc_triangle B ω hω a c b hc.1 h1
    refine ⟨h3, ?_⟩
    rw [murotaWalkWeight_cons_cons]
    linarith

/-- The cycle inequality: every closed walk of the exchange graph at `x` has weight `≤ 0`. -/
theorem murota_exc_no_positive_cycle {V : Type*} [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B) :
    ∀ L : List V, L.IsChain (fun u v => x - chi u + chi v ∈ B) → L.head? = L.getLast? →
      murotaWalkWeight (fun u v => ω (x - chi u + chi v) - ω x) L ≤ 0
  | [], _, _ => le_of_eq (murotaWalkWeight_nil _)
  | a :: L, hc, hl => by
    have hl' : (a :: L).getLast? = some a := by rw [← hl]; rfl
    have h := (murota_exc_walk_le B ω hω hx L a a hc hl').2
    rw [sub_add_cancel, sub_self] at h
    exact h

/-! ### S2.4 Deliverable: Lemma 4.5 (supergradient at every point of `B`) -/

/-- **Murota 1996, Lemma 4.5.** Under (EXC), every `x ∈ B` has a supergradient `p`:
`ω y ≤ ω x + ⟨p, y − x⟩` for all `y ∈ B`. -/
theorem murota_exists_supergradient {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B) :
    ∃ p : V → ℝ, ∀ y ∈ B, ω y ≤ ω x + pairing p (toReal y - toReal x) := by
  obtain ⟨p, hp⟩ := murota_exists_potential (fun u v => x - chi u + chi v ∈ B)
    (fun u v => ω (x - chi u + chi v) - ω x) (murota_exc_no_positive_cycle B ω hω hx)
  refine ⟨p, fun y hy => ?_⟩
  have hloc : ∀ u v : V, x - chi u + chi v ∈ B →
      perturb ω (-p) (x - chi u + chi v) ≤ perturb ω (-p) x := by
    intro u v huv
    have h := hp u v huv
    unfold perturb
    rw [murota_pairing_toReal_exchange, Pi.neg_apply, Pi.neg_apply]
    linarith
  have key := murota_local_opt B (perturb ω (-p)) (murota_perturb_satisfiesEXC B ω hω (-p)) hx
    hloc y hy
  unfold perturb at key
  rw [murota_pairing_neg_left, murota_pairing_neg_left] at key
  rw [murota_pairing_sub_right]
  linarith

/-- Lemma 4.5, argmax form: every `x ∈ B` maximises some perturbation `ω[p]` on `B`. -/
theorem murota_mem_argmaxB_of_exc {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B) :
    ∃ p : V → ℝ, x ∈ argmaxB B (perturb ω p) := by
  obtain ⟨p, hp⟩ := murota_exists_supergradient B ω hω hx
  refine ⟨-p, ?_⟩
  rw [argmaxB, Finset.mem_filter]
  refine ⟨hx, fun y hy => ?_⟩
  have h := hp y hy
  unfold perturb
  rw [murota_pairing_neg_left, murota_pairing_neg_left]
  rw [murota_pairing_sub_right] at h
  linarith

/-- Consequence of Lemma 4.5: under (EXC) the concave closure agrees with `ω` on `B`. -/
theorem murota_concaveClosure_eq_of_exc {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B) :
    concaveClosure B ω (toReal x) = ω x := by
  obtain ⟨p, hp⟩ := murota_exists_supergradient B ω hω hx
  have hB : B.Nonempty := ⟨x, hx⟩
  have hxhull : toReal x ∈ hull B := subset_convexHull ℝ _ ⟨x, Finset.mem_coe.mpr hx, rfl⟩
  refine le_antisymm ?_ (murota_le_concaveClosure B ω hx)
  have h1 := murota_concaveClosure_le B hB ω hxhull p
  obtain ⟨y, hy, hye⟩ := murota_exists_concaveConj_eq B hB ω p
  have h2 := hp y hy
  rw [murota_pairing_sub_right] at h2
  rw [hye] at h1
  linarith


end Sol2f8a2c6e

open SteinitzExchange.LocalSupermod in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    ∀ x ∈ B, concaveClosure B ω (toReal x) = ω x := by
  intro x hx
  exact Sol2f8a2c6e.murota_concaveClosure_eq_of_exc B ω hω hx
