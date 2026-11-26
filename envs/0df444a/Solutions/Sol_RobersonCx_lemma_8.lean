-- Prove2me | solution 1 for RobersonCx.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @세리나
-- created : 2026-11-26T16:59:13.092941+00:00
-- url     : https://prove2.me/submissions/2ab38665-2315-4d74-ba21-50d4e47797b1

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Data.ZMod.Basic
import Definitions.Def_RobersonCx_QuotIsoTo
import Definitions.Def_RobersonCx_circulantD

set_option autoImplicit false

open RobersonCx

private def reduceIndex (q m : ℕ) : ZMod (q * m) →+* ZMod q :=
  ZMod.castHom (dvd_mul_right q m) (ZMod q)

private theorem reduce_fibers {q m : ℕ} (a b : ZMod (q * m)) :
    reduceIndex q m a = reduceIndex q m b ↔
      ∃ z : ℤ, a = b + z • (q : ZMod (q * m)) := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := ZMod.intCast_surjective (a - b)
    have hz : (w : ZMod q) = 0 := by
      calc
        (w : ZMod q) = reduceIndex q m (w : ZMod (q * m)) := (map_intCast _ _).symm
        _ = 0 := by rw [hw, map_sub, h, sub_self]
    obtain ⟨z, hzw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd w q).mp hz
    have hdiff : (q : ZMod (q * m)) * (z : ZMod (q * m)) = a - b := by
      simpa only [hzw, Int.cast_mul, Int.cast_natCast] using hw
    refine ⟨z, ?_⟩
    calc
      a = b + (a - b) := by abel
      _ = b + (q : ZMod (q * m)) * (z : ZMod (q * m)) := by rw [hdiff]
      _ = b + z • (q : ZMod (q * m)) := by
        rw [zsmul_eq_mul]
        exact congrArg (b + ·) (mul_comm (q : ZMod (q * m)) (z : ZMod (q * m)))
  · rintro ⟨z, rfl⟩
    rw [map_add, map_zsmul, map_natCast, ZMod.natCast_self, zsmul_zero, add_zero]

private theorem shift_order (q m : ℕ) (hq : 0 < q) (hm : 0 < m) :
    orderOf (Multiplicative.ofAdd (q : ZMod (q * m))) = m := by
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_coe q (Nat.mul_pos hq hm).ne',
    Nat.gcd_eq_right (dvd_mul_right q m), Nat.mul_div_cancel_left m hq]

private def permHom {A : Type} (G : SimpleGraph A) : (G ≃g G) →* Equiv.Perm A where
  toFun e := e.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem orbit_iff_zpow {A : Type} (τ : Equiv.Perm A) (a b : A) :
    MulAction.orbitRel (Subgroup.zpowers τ) A a b ↔ ∃ z : ℤ, (τ ^ z) b = a := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨z, hz⟩ := g.property
    exact ⟨z, (congrArg (fun π : Equiv.Perm A => π b) hz).trans hg⟩
  · rintro ⟨z, hz⟩
    exact ⟨⟨τ ^ z, ⟨z, rfl⟩⟩, hz⟩

private theorem quotient_iso_of_projection {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B)
    (τ : Equiv.Perm A) (f : A → B) (hsurj : Function.Surjective f)
    (hfibers : ∀ a b, MulAction.orbitRel (Subgroup.zpowers τ) A a b ↔ f a = f b)
    (hmap : ∀ ⦃a b⦄, G.Adj a b → H.Adj (f a) (f b))
    (hlift : ∀ a b, H.Adj (f a) b → ∃ v, f v = b ∧ G.Adj a v) :
    QuotIsoTo G τ H := by
  let project : OrbitQuot τ → B :=
    Quotient.lift f (fun a b hab => (hfibers a b).mp hab)
  have hinj : Function.Injective project := by
    intro O P
    refine Quotient.inductionOn₂ O P ?_
    intro a b hab
    exact Quotient.sound ((hfibers a b).mpr hab)
  have honto : Function.Surjective project := by
    intro b
    obtain ⟨a, ha⟩ := hsurj b
    exact ⟨Quotient.mk _ a, ha⟩
  let e := Equiv.ofBijective project ⟨hinj, honto⟩
  refine ⟨e, ?_⟩
  intro O P
  constructor
  · rintro ⟨u, v, rfl, rfl, huv⟩
    exact hmap huv
  · intro hadj
    obtain ⟨u, rfl⟩ := Quotient.exists_rep O
    obtain ⟨v, hv, huv⟩ := hlift u (e P) hadj
    exact ⟨u, v, rfl, e.injective hv, huv⟩

private def rotateD (n r : ℕ) : Multiplicative (ZMod n) →*
    (circulantD n r ≃g circulantD n r) where
  toFun t :=
    { __ := Equiv.addRight t.toAdd
      map_rel_iff' := by
        intro a b
        exact SimpleGraph.circulantGraph_adj_translate }
  map_one' := by
    apply DFunLike.ext
    intro a
    change a + (0 : ZMod n) = a
    exact add_zero _
  map_mul' s t := by
    apply DFunLike.ext
    intro a
    change a + (s.toAdd + t.toAdd) = a + t.toAdd + s.toAdd
    ac_rfl

private theorem split_adj_right_left {n r : ℕ} (a b : ZMod n) :
    (splitB n r).Adj (Sum.inr a) (Sum.inl b) ↔ b = a ∨ b = a + 1 ∨ b = a + r := by
  simp [splitB, SimpleGraph.fromRel_adj, splitRel]

private theorem split_adj_left_right {n r : ℕ} (a b : ZMod n) :
    (splitB n r).Adj (Sum.inl b) (Sum.inr a) ↔ b = a ∨ b = a + 1 ∨ b = a + r := by
  rw [SimpleGraph.adj_comm, split_adj_right_left]

private theorem shifted_eq {n : ℕ} (a b t d : ZMod n) :
    b + t = (a + t) + d ↔ b = a + d := by
  rw [show a + t + d = a + d + t by ac_rfl, add_right_cancel_iff]

private def rotateB (n r : ℕ) : Multiplicative (ZMod n) →*
    (splitB n r ≃g splitB n r) where
  toFun t :=
    { __ := Equiv.sumCongr (Equiv.addRight t.toAdd) (Equiv.addRight t.toAdd)
      map_rel_iff' := by
        intro a b
        cases a with
        | inl a =>
          cases b with
          | inl b =>
            change (splitB n r).Adj (Sum.inl (a + t.toAdd)) (Sum.inl (b + t.toAdd)) ↔ _
            simp [splitB, SimpleGraph.fromRel_adj, splitRel]
          | inr b =>
            change (splitB n r).Adj (Sum.inl (a + t.toAdd)) (Sum.inr (b + t.toAdd)) ↔ _
            simp only [split_adj_left_right, add_right_cancel_iff, shifted_eq]
        | inr a =>
          cases b with
          | inl b =>
            change (splitB n r).Adj (Sum.inr (a + t.toAdd)) (Sum.inl (b + t.toAdd)) ↔ _
            simp only [split_adj_right_left, add_right_cancel_iff, shifted_eq]
          | inr b =>
            change (splitB n r).Adj (Sum.inr (a + t.toAdd)) (Sum.inr (b + t.toAdd)) ↔ _
            simp [splitB, SimpleGraph.fromRel_adj, splitRel] }
  map_one' := by
    apply DFunLike.ext
    intro v
    cases v with
    | inl a =>
      change Sum.inl (a + (0 : ZMod n)) = Sum.inl a
      rw [add_zero]
    | inr a =>
      change Sum.inr (a + (0 : ZMod n)) = Sum.inr a
      rw [add_zero]
  map_mul' s t := by
    apply DFunLike.ext
    intro v
    cases v with
    | inl a =>
      change Sum.inl (a + (s.toAdd + t.toAdd)) = Sum.inl (a + t.toAdd + s.toAdd)
      congr 1
      ac_rfl
    | inr a =>
      change Sum.inr (a + (s.toAdd + t.toAdd)) = Sum.inr (a + t.toAdd + s.toAdd)
      congr 1
      ac_rfl

private theorem rotateD_inj (n r : ℕ) : Function.Injective (rotateD n r) := by
  intro s t h
  have hv := DFunLike.congr_fun h (0 : ZMod n)
  change 0 + s.toAdd = 0 + t.toAdd at hv
  exact congrArg Multiplicative.ofAdd (by simpa only [zero_add] using hv : s.toAdd = t.toAdd)

private theorem rotateB_inj (n r : ℕ) : Function.Injective (rotateB n r) := by
  intro s t h
  have hv := DFunLike.congr_fun h (Sum.inl (0 : ZMod n) : ZMod n ⊕ ZMod n)
  change (Sum.inl (0 + s.toAdd) : ZMod n ⊕ ZMod n) = Sum.inl (0 + t.toAdd) at hv
  exact congrArg Multiplicative.ofAdd (by simpa only [zero_add, Sum.inl.injEq] using hv :
    s.toAdd = t.toAdd)

private theorem rotateD_zpow (n r : ℕ) (t v : ZMod n) (z : ℤ) :
    ((rotateD n r (Multiplicative.ofAdd t)).toEquiv ^ z) v = v + z • t := by
  let f := (permHom (circulantD n r)).comp (rotateD n r)
  change (f (Multiplicative.ofAdd t) ^ z) v = _
  rw [← map_zpow]
  change v + ((Multiplicative.ofAdd t) ^ z).toAdd = _
  rfl

private theorem rotateB_zpow (n r : ℕ) (t : ZMod n) (v : ZMod n ⊕ ZMod n) (z : ℤ) :
    ((rotateB n r (Multiplicative.ofAdd t)).toEquiv ^ z) v =
      Sum.map (fun a => a + z • t) (fun a => a + z • t) v := by
  let f := (permHom (splitB n r)).comp (rotateB n r)
  change (f (Multiplicative.ofAdd t) ^ z) v = _
  rw [← map_zpow]
  cases v with
  | inl v =>
    change Sum.inl (v + ((Multiplicative.ofAdd t) ^ z).toAdd) = Sum.inl (v + z • t)
    rfl
  | inr v =>
    change Sum.inr (v + ((Multiplicative.ofAdd t) ^ z).toAdd) = Sum.inr (v + z • t)
    rfl

private theorem circulant_adj_steps {n r : ℕ} (a b : ZMod n) :
    (circulantD n r).Adj a b ↔
      a ≠ b ∧ ∃ k : ℕ, (k = 1 ∨ k = r) ∧ (a - b = k ∨ b - a = k) := by
  simp only [circulantD, SimpleGraph.circulantGraph_adj, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hne, (h | h) | (h | h)⟩
    · exact ⟨hne, 1, .inl rfl, .inl (by simpa only [Nat.cast_one] using h)⟩
    · exact ⟨hne, r, .inr rfl, .inl h⟩
    · exact ⟨hne, 1, .inl rfl, .inr (by simpa only [Nat.cast_one] using h)⟩
    · exact ⟨hne, r, .inr rfl, .inr h⟩
  · rintro ⟨hne, k, hk, h⟩
    rcases hk with rfl | rfl
    · simp only [Nat.cast_one] at h
      tauto
    · tauto

private theorem reduceD_preserves {r q m : ℕ} (hr : 2 ≤ r) (hq : 2 * r < q)
    {a b : ZMod (q * m)} (h : (circulantD (q * m) r).Adj a b) :
    (circulantD q r).Adj (reduceIndex q m a) (reduceIndex q m b) := by
  obtain ⟨_, k, hk, hd⟩ := (circulant_adj_steps a b).mp h
  have hpos : 0 < k := by rcases hk with rfl | rfl <;> omega
  have hlt : k < q := by rcases hk with rfl | rfl <;> omega
  have hnonzero : (k : ZMod q) ≠ 0 := by
    intro eq
    exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos ((ZMod.natCast_eq_zero_iff k q).mp eq))
  have hdiff :
      reduceIndex q m a - reduceIndex q m b = k ∨ reduceIndex q m b - reduceIndex q m a = k :=
    hd.elim
      (fun ha => .inl (by simpa only [map_sub, map_natCast] using congrArg (reduceIndex q m) ha))
      (fun hb => .inr (by simpa only [map_sub, map_natCast] using congrArg (reduceIndex q m) hb))
  refine (circulant_adj_steps _ _).mpr ⟨?_, k, hk, hdiff⟩
  intro eq
  simp only [eq, sub_self] at hdiff
  exact hdiff.elim (fun hzero => hnonzero hzero.symm) (fun hzero => hnonzero hzero.symm)

private theorem reduceD_lifts {r q m : ℕ} (a : ZMod (q * m)) (b : ZMod q)
    (hab : (circulantD q r).Adj (reduceIndex q m a) b) :
    ∃ v, reduceIndex q m v = b ∧ (circulantD (q * m) r).Adj a v := by
  obtain ⟨hne, k, hk, hd⟩ := (circulant_adj_steps _ _).mp hab
  rcases hd with hd | hd
  · have hv : reduceIndex q m (a - k) = b := by
      rw [map_sub, map_natCast]
      linear_combination hd
    refine ⟨a - k, hv, (circulant_adj_steps _ _).mpr ⟨?_, k, hk, .inl ?_⟩⟩
    · intro eq
      exact hne ((congrArg (reduceIndex q m) eq).trans hv)
    · abel
  · have hv : reduceIndex q m (a + k) = b := by
      rw [map_add, map_natCast]
      linear_combination -hd
    refine ⟨a + k, hv, (circulant_adj_steps _ _).mpr ⟨?_, k, hk, .inr ?_⟩⟩
    · intro eq
      exact hne ((congrArg (reduceIndex q m) eq).trans hv)
    · abel

private theorem split_adj_steps {n r : ℕ} (a b : ZMod n) :
    (splitB n r).Adj (Sum.inr a) (Sum.inl b) ↔
      ∃ k : ℕ, (k = 0 ∨ k = 1 ∨ k = r) ∧ b = a + k := by
  rw [split_adj_right_left]
  constructor
  · rintro (h | h | h)
    · exact ⟨0, .inl rfl, by simpa only [Nat.cast_zero, add_zero] using h⟩
    · exact ⟨1, .inr (.inl rfl), by simpa only [Nat.cast_one] using h⟩
    · exact ⟨r, .inr (.inr rfl), h⟩
  · rintro ⟨k, (rfl | rfl | rfl), h⟩
    · exact .inl (by simpa only [Nat.cast_zero, add_zero] using h)
    · exact .inr (.inl (by simpa only [Nat.cast_one] using h))
    · exact .inr (.inr h)

private def reduceSplit (q m : ℕ) : ZMod (q * m) ⊕ ZMod (q * m) → ZMod q ⊕ ZMod q :=
  Sum.map (reduceIndex q m) (reduceIndex q m)

private theorem reduceSplit_surjective (q m : ℕ) : Function.Surjective (reduceSplit q m) := by
  intro b
  cases b with
  | inl b =>
    obtain ⟨a, ha⟩ := ZMod.castHom_surjective (dvd_mul_right q m) b
    exact ⟨Sum.inl a, congrArg Sum.inl ha⟩
  | inr b =>
    obtain ⟨a, ha⟩ := ZMod.castHom_surjective (dvd_mul_right q m) b
    exact ⟨Sum.inr a, congrArg Sum.inr ha⟩

private theorem reduceSplit_preserves {q m r : ℕ} {a b : ZMod (q * m) ⊕ ZMod (q * m)}
    (hab : (splitB (q * m) r).Adj a b) : (splitB q r).Adj (reduceSplit q m a) (reduceSplit q m b) := by
  have cross {i j : ZMod (q * m)} (h : (splitB _ r).Adj (Sum.inr i) (Sum.inl j)) :
      (splitB q r).Adj (Sum.inr (reduceIndex q m i)) (Sum.inl (reduceIndex q m j)) := by
    obtain ⟨k, hk, hj⟩ := (split_adj_steps i j).mp h
    refine (split_adj_steps _ _).mpr ⟨k, hk, ?_⟩
    simpa only [map_add, map_natCast] using congrArg (reduceIndex q m) hj
  cases a with
  | inl a =>
    cases b with
    | inl b => simp [splitB, SimpleGraph.fromRel_adj, splitRel] at hab
    | inr b => exact (cross hab.symm).symm
  | inr a =>
    cases b with
    | inl b => exact cross hab
    | inr b => simp [splitB, SimpleGraph.fromRel_adj, splitRel] at hab

private theorem reduceSplit_lifts {q m r : ℕ} (a : ZMod (q * m) ⊕ ZMod (q * m))
    (b : ZMod q ⊕ ZMod q) (hab : (splitB q r).Adj (reduceSplit q m a) b) :
    ∃ v, reduceSplit q m v = b ∧ (splitB (q * m) r).Adj a v := by
  cases a with
  | inl a =>
    cases b with
    | inl b => simp [reduceSplit, splitB, SimpleGraph.fromRel_adj, splitRel] at hab
    | inr b =>
      have h : (splitB q r).Adj (Sum.inr b) (Sum.inl (reduceIndex q m a)) := hab.symm
      obtain ⟨k, hk, h⟩ := (split_adj_steps b _).mp h
      refine ⟨Sum.inr (a - k), ?_, ((split_adj_steps _ _).mpr ⟨k, hk, ?_⟩).symm⟩
      · change Sum.inr (reduceIndex q m (a - k)) = Sum.inr b
        apply congrArg Sum.inr
        rw [map_sub, map_natCast]
        linear_combination h
      · abel
  | inr a =>
    cases b with
    | inl b =>
      have h : (splitB q r).Adj (Sum.inr (reduceIndex q m a)) (Sum.inl b) := hab
      obtain ⟨k, hk, h⟩ := (split_adj_steps _ b).mp h
      refine ⟨Sum.inl (a + k), ?_, (split_adj_steps _ _).mpr ⟨k, hk, rfl⟩⟩
      change Sum.inl (reduceIndex q m (a + k)) = Sum.inl b
      rw [map_add, map_natCast, h]
    | inr b => simp [reduceSplit, splitB, SimpleGraph.fromRel_adj, splitRel] at hab

theorem solution (r q m : ℕ) (hr : 2 ≤ r) (hq : 2 * r < q) (hm : 0 < m) :
    (∃ σ : circulantD (q * m) r ≃g circulantD (q * m) r,
      orderOf σ = m ∧ QuotIsoTo (circulantD (q * m) r) σ.toEquiv (circulantD q r)) ∧
    (∃ σ : splitB (q * m) r ≃g splitB (q * m) r,
      orderOf σ = m ∧ QuotIsoTo (splitB (q * m) r) σ.toEquiv (splitB q r)) := by
  have hq0 : 0 < q := by omega
  let step : Multiplicative (ZMod (q * m)) := Multiplicative.ofAdd (q : ZMod (q * m))
  refine ⟨⟨rotateD (q * m) r step, ?_, ?_⟩, ⟨rotateB (q * m) r step, ?_, ?_⟩⟩
  · exact (orderOf_injective _ (rotateD_inj _ _) _).trans (shift_order q m hq0 hm)
  · refine quotient_iso_of_projection _ _ _ (reduceIndex q m)
      (ZMod.castHom_surjective (dvd_mul_right q m)) ?_
      (by intro a b hab; exact reduceD_preserves hr hq hab) reduceD_lifts
    intro a b
    rw [orbit_iff_zpow, reduce_fibers]
    simp only [step, rotateD_zpow]
    exact exists_congr (fun _ => eq_comm)
  · exact (orderOf_injective _ (rotateB_inj _ _) _).trans (shift_order q m hq0 hm)
  · refine quotient_iso_of_projection _ _ _ (reduceSplit q m)
      (reduceSplit_surjective q m) ?_
      (by intro a b hab; exact reduceSplit_preserves hab) reduceSplit_lifts
    intro a b
    rw [orbit_iff_zpow]
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        simp only [step, rotateB_zpow, reduceSplit, Sum.map_inl, Sum.inl.injEq]
        rw [reduce_fibers]
        exact exists_congr (fun _ => eq_comm)
      | inr b => simp [step, rotateB_zpow, reduceSplit]
    | inr a =>
      cases b with
      | inl b => simp [step, rotateB_zpow, reduceSplit]
      | inr b =>
        simp only [step, rotateB_zpow, reduceSplit, Sum.map_inr, Sum.inr.injEq]
        rw [reduce_fibers]
        exact exists_congr (fun _ => eq_comm)
