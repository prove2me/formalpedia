-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P12.ordinary_conjugates_commute
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T06:16:41.439112+00:00
-- url     : https://prove2.me/submissions/769fb2e7-d19d-4506-b9ce-f36d823e5ef0

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support21.P12

theorem g66n2_conj {A : Type*} [Ring A] (x x' w w' Y : A) (hww : w * w' = 1) (hw'w : w' * w = 1)
    (hx : x * w = w * x') (hc : Commute x' Y) : Commute x (w * Y * w') := by
  have h2 : x' * w' = w' * x := by
    calc x' * w' = (w' * w) * x' * w' := by rw [hw'w, one_mul]
      _ = w' * (x * w) * w' := by rw [hx]; noncomm_ring
      _ = w' * x * (w * w') := by noncomm_ring
      _ = w' * x := by rw [hww, mul_one]
  show x * (w * Y * w') = w * Y * w' * x
  calc x * (w * Y * w') = (x * w) * Y * w' := by noncomm_ring
    _ = w * (x' * Y) * w' := by rw [hx]; noncomm_ring
    _ = w * Y * (x' * w') := by rw [hc.eq]; noncomm_ring
    _ = w * Y * w' * x := by rw [h2]; noncomm_ring

section Gen
variable {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (n : ℕ) (g gi e : ℕ → A) (y : A)
  (c ri rr : S)

structure g66n2_Rels : Prop where
  inv1 : ∀ k, k + 1 < n → g k * gi k = 1
  inv2 : ∀ k, k + 1 < n → gi k * g k = 1
  braid : ∀ k, k + 2 < n → g k * g (k+1) * g k = g (k+1) * g k * g (k+1)
  far : ∀ k l, k + 1 < n → l + 1 < n → (k + 1 < l ∨ l + 1 < k) → g k * g l = g l * g k
  farGE : ∀ k l, k + 1 < n → l + 1 < n → (k + 1 < l ∨ l + 1 < k) → g k * e l = e l * g k
  farEE : ∀ k l, k + 1 < n → l + 1 < n → (k + 1 < l ∨ l + 1 < k) → e k * e l = e l * e k
  yg : ∀ k, k + 1 < n → 1 ≤ k → y * g k = g k * y
  ye : ∀ k, k + 1 < n → 1 ≤ k → y * e k = e k * y
  ge : ∀ k, k + 1 < n → g k * e k = ri • e k
  eg : ∀ k, k + 1 < n → e k * g k = ri • e k
  ege : ∀ a b, a + 1 < n → b + 1 < n → (a + 1 = b ∨ b + 1 = a) → e a * g b * e a = rr • e a
  gge : ∀ a b, a + 1 < n → b + 1 < n → (a + 1 = b ∨ b + 1 = a) → g a * g b * e a = e b * e a
  egg : ∀ a b, a + 1 < n → b + 1 < n → (a + 1 = b ∨ b + 1 = a) → e a * g b * g a = e a * e b
  sk : ∀ k, k + 1 < n → gi k = g k - c • (1 - e k)
  rr1 : rr * ri = 1

variable {n g gi e y c ri rr}

theorem g66n2_comm_gi (H : g66n2_Rels n g gi e y c ri rr) (x : A) (k : ℕ) (hk : k + 1 < n)
    (h : Commute x (g k)) : Commute x (gi k) := by
  have := Commute.units_inv_right (u := ⟨g k, gi k, H.inv1 k hk, H.inv2 k hk⟩) h
  exact this

theorem g66n2_low (H : g66n2_Rels n g gi e y c ri rr) (i : ℕ) (hi : i + 1 < n) (rev : Bool) :
    ∀ j, j < i → Commute (g i) (conjugateY g gi y rev j) ∧
      Commute (e i) (conjugateY g gi y rev j) := by
  intro j
  induction j with
  | zero =>
    intro h0
    exact ⟨(H.yg i hi (by omega)).symm, (H.ye i hi (by omega)).symm⟩
  | succ j ih =>
    intro hj
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have c1 : Commute (g i) (g j) := H.far i j hi (by omega) (by omega)
    have c2 : Commute (e i) (g j) := (H.farGE j i (by omega) hi (by omega)).symm
    have c1' := g66n2_comm_gi H _ j (by omega) c1
    have c2' := g66n2_comm_gi H _ j (by omega) c2
    simp only [conjugateY]
    cases rev
    · exact ⟨(c1.mul_right ih1).mul_right c1', (c2.mul_right ih2).mul_right c2'⟩
    · exact ⟨(c1'.mul_right ih1).mul_right c1, (c2'.mul_right ih2).mul_right c2⟩

theorem g66n2_ei (H : g66n2_Rels n g gi e y c ri rr) (k : ℕ) (hk : k + 1 < n) :
    gi k * e k = rr • e k := by
  have := congrArg (gi k * ·) (H.ge k hk)
  simp only [← mul_assoc, H.inv2 k hk, one_mul, mul_smul_comm] at this
  have h2 := congrArg (rr • ·) this
  simp only [smul_smul, H.rr1, one_smul] at h2
  exact h2.symm

theorem g66n2_ie (H : g66n2_Rels n g gi e y c ri rr) (k : ℕ) (hk : k + 1 < n) :
    e k * gi k = rr • e k := by
  have := congrArg (· * gi k) (H.eg k hk)
  simp only [mul_assoc, H.inv1 k hk, mul_one, smul_mul_assoc] at this
  have h2 := congrArg (rr • ·) this
  simp only [smul_smul, H.rr1, one_smul] at h2
  exact h2.symm

theorem g66n2_G1 (H : g66n2_Rels n g gi e y c ri rr) (a b : ℕ) (ha : a + 1 < n) (hb : b + 1 < n)
    (hab : a + 1 = b ∨ b + 1 = a) : gi a * gi b * e a = e b * e a := by
  have e1 := g66n2_ei H a ha
  have e2 : gi a * (e b * e a) = g b * e a := by
    rw [← H.gge a b ha hb hab, ← mul_assoc, ← mul_assoc, H.inv2 a ha, one_mul]
  have e3 : e a * (g b * e a) = rr • e a := by rw [← mul_assoc]; exact H.ege a b ha hb hab
  have e4 : g a * (g b * e a) = e b * e a := by rw [← mul_assoc]; exact H.gge a b ha hb hab
  calc gi a * gi b * e a = gi a * ((g b - c • (1 - e b)) * e a) := by rw [← H.sk b hb, mul_assoc]
    _ = gi a * (g b * e a) - c • (gi a * e a) + c • (gi a * (e b * e a)) := by
        simp only [sub_mul, smul_mul_assoc, one_mul, mul_sub, mul_smul_comm]; module
    _ = (g a - c • (1 - e a)) * (g b * e a) - c • (rr • e a) + c • (g b * e a) := by
        rw [e1, e2, H.sk a ha]
    _ = g a * (g b * e a) - c • (g b * e a) + c • (e a * (g b * e a)) - c • (rr • e a)
          + c • (g b * e a) := by
        simp only [sub_mul, smul_mul_assoc, one_mul]; module
    _ = e b * e a := by rw [e4, e3]; module

theorem g66n2_G2 (H : g66n2_Rels n g gi e y c ri rr) (a b : ℕ) (ha : a + 1 < n) (hb : b + 1 < n)
    (hab : a + 1 = b ∨ b + 1 = a) : e a * gi b * gi a = e a * e b := by
  have e1 := g66n2_ie H a ha
  have e2 : e a * e b * gi a = e a * g b := by
    rw [← H.egg a b ha hb hab, mul_assoc, H.inv1 a ha, mul_one]
  have e3 : e a * g b * e a = rr • e a := H.ege a b ha hb hab
  calc e a * gi b * gi a = e a * (g b - c • (1 - e b)) * gi a := by rw [← H.sk b hb]
    _ = e a * g b * gi a - c • (e a * gi a) + c • (e a * e b * gi a) := by
        simp only [sub_mul, smul_mul_assoc, one_mul, mul_sub, mul_smul_comm, mul_one]; module
    _ = e a * g b * (g a - c • (1 - e a)) - c • (rr • e a) + c • (e a * g b) := by
        rw [e1, e2, H.sk a ha]
    _ = e a * g b * g a - c • (e a * g b) + c • (e a * g b * e a) - c • (rr • e a)
          + c • (e a * g b) := by
        simp only [mul_sub, mul_smul_comm, mul_one]; module
    _ = e a * e b := by rw [H.egg a b ha hb hab, e3]; module

theorem g66n2_M2 (H : g66n2_Rels n g gi e y c ri rr) (i : ℕ) (hi : i + 2 < n) :
    g i * (gi (i+1) * gi i) = gi (i+1) * gi i * g (i+1) := by
  have i1 := H.inv1 i (by omega)
  have i2 := H.inv2 i (by omega)
  have j1 := H.inv1 (i+1) (by omega)
  have j2 := H.inv2 (i+1) (by omega)
  have hb := H.braid i hi
  have : g (i+1) = g i * g (i+1) * g i * gi (i+1) * gi i := by
    calc g (i+1) = g (i+1) * g i * g (i+1) * gi (i+1) * gi i := by
          rw [mul_assoc (g (i+1) * g i), j1, mul_one, mul_assoc, i1, mul_one]
      _ = _ := by rw [hb]
  calc g i * (gi (i+1) * gi i) = gi (i+1) * gi i * (g i * g (i+1) * g i * gi (i+1) * gi i) := by
        simp only [← mul_assoc]
        rw [mul_assoc (gi (i+1)) (gi i) (g i), i2, mul_one, j2, one_mul]
    _ = _ := by rw [← this]

theorem g66n2_base (H : g66n2_Rels n g gi e y c ri rr) (i : ℕ) (hi : i + 2 < n) (rev : Bool) :
    Commute (g i) (conjugateY g gi y rev (i+2)) ∧ Commute (e i) (conjugateY g gi y rev (i+2)) := by
  obtain ⟨l1, l2⟩ := g66n2_low H (i+1) (by omega) rev i (by omega)
  have i1 := H.inv1 i (by omega)
  have i2 := H.inv2 i (by omega)
  have j1 := H.inv1 (i+1) (by omega)
  have j2 := H.inv2 (i+1) (by omega)
  cases rev
  · have hY : conjugateY g gi y false (i+2) =
        (g (i+1) * g i) * conjugateY g gi y false i * (gi i * gi (i+1)) := by
      simp only [conjugateY]; simp only [Bool.false_eq_true, if_false]; noncomm_ring
    have hww : (g (i+1) * g i) * (gi i * gi (i+1)) = 1 := by
      rw [mul_assoc, ← mul_assoc (g i), i1, one_mul, j1]
    have hw'w : (gi i * gi (i+1)) * (g (i+1) * g i) = 1 := by
      rw [mul_assoc, ← mul_assoc (gi (i+1)), j2, one_mul, i2]
    rw [hY]
    refine ⟨g66n2_conj _ (g (i+1)) _ _ _ hww hw'w ?_ l1, g66n2_conj _ (e (i+1)) _ _ _ hww hw'w ?_ l2⟩
    · rw [← mul_assoc, H.braid i hi]
    · rw [← mul_assoc, H.egg i (i+1) (by omega) (by omega) (by omega),
        H.gge (i+1) i (by omega) (by omega) (by omega)]
  · have hY : conjugateY g gi y true (i+2) =
        (gi (i+1) * gi i) * conjugateY g gi y true i * (g i * g (i+1)) := by
      simp only [conjugateY]; simp only [if_true]; noncomm_ring
    have hww : (gi (i+1) * gi i) * (g i * g (i+1)) = 1 := by
      rw [mul_assoc, ← mul_assoc (gi i), i2, one_mul, j2]
    have hw'w : (g i * g (i+1)) * (gi (i+1) * gi i) = 1 := by
      rw [mul_assoc, ← mul_assoc (g (i+1)), j1, one_mul, i1]
    rw [hY]
    refine ⟨g66n2_conj _ (g (i+1)) _ _ _ hww hw'w ?_ l1, g66n2_conj _ (e (i+1)) _ _ _ hww hw'w ?_ l2⟩
    · exact g66n2_M2 H i hi
    · rw [← mul_assoc, g66n2_G2 H i (i+1) (by omega) (by omega) (by omega),
        g66n2_G1 H (i+1) i (by omega) (by omega) (by omega)]

theorem g66n2_high (H : g66n2_Rels n g gi e y c ri rr) (i : ℕ) (hi : i + 1 < n) (rev : Bool) :
    ∀ j, i + 2 ≤ j → j < n → Commute (g i) (conjugateY g gi y rev j) ∧
      Commute (e i) (conjugateY g gi y rev j) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro h; exact g66n2_base H i h rev
  | succ j hj ih =>
    intro hjn
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have c1 : Commute (g i) (g j) := H.far i j hi (by omega) (by omega)
    have c2 : Commute (e i) (g j) := (H.farGE j i (by omega) hi (by omega)).symm
    have c1' := g66n2_comm_gi H _ j (by omega) c1
    have c2' := g66n2_comm_gi H _ j (by omega) c2
    simp only [conjugateY]
    cases rev
    · exact ⟨(c1.mul_right ih1).mul_right c1', (c2.mul_right ih2).mul_right c2'⟩
    · exact ⟨(c1'.mul_right ih1).mul_right c1, (c2'.mul_right ih2).mul_right c2⟩

theorem g66n2_cc (H : g66n2_Rels n g gi e y c ri rr) : ConjugateCommutation n g gi e y := by
  intro i j hi hj hji hji1 rev
  rcases lt_or_ge j i with h | h
  · exact (g66n2_low H i hi rev j h).symm
  · exact (g66n2_high H i hi rev j (by omega) hj).symm

end Gen

theorem g66n2_cY_map {S A B : Type*} [CommRing S] [Ring A] [Algebra S A] [Ring B] [Algebra S B]
    (f : A →ₐ[S] B) (g gi : ℕ → A) (y : A) (rev : Bool) (j : ℕ) :
    conjugateY (fun k => f (g k)) (fun k => f (gi k)) (f y) rev j = f (conjugateY g gi y rev j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [conjugateY, ih]
    split_ifs <;> simp [map_mul]

theorem g66n2_cc_map {S A B : Type*} [CommRing S] [Ring A] [Algebra S A] [Ring B] [Algebra S B]
    (f : A →ₐ[S] B) (n : ℕ) (g gi e : ℕ → A) (y : A) (h : ConjugateCommutation n g gi e y) :
    ConjugateCommutation n (fun k => f (g k)) (fun k => f (gi k)) (fun k => f (e k)) (f y) := by
  intro i j hi hj hji hji1 rev
  rw [g66n2_cY_map]
  obtain ⟨h1, h2⟩ := h i j hi hj hji hji1 rev
  exact ⟨h1.map f, h2.map f⟩

theorem g66n2_wR (S : Type*) [CommRing S] (omega : ℕ → S) (rho q : Sˣ) (m : ℕ) :
    g66n2_Rels m (fun k => wMap S omega rho q m (wg S m k)) (fun k => wMap S omega rho q m (wgi S m k))
      (fun k => wMap S omega rho q m (we S m k)) (wMap S omega rho q m (wy S m))
      ((↑q : S) - ↑(q⁻¹)) (↑(rho⁻¹) : S) (↑rho : S) := by
  have q' : ∀ {x y}, WRel S omega rho q m x y → wMap S omega rho q m x = wMap S omega rho q m y :=
    fun h => RingQuot.mkAlgHom_rel S h
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k l hk hl hd => ?_,
    fun k l hk hl hd => ?_, fun k l hk hl hd => ?_, fun k hk hp => ?_, fun k hk hp => ?_,
    fun k hk => ?_, fun k hk => ?_, fun a b ha hb hab => ?_, fun a b ha hb hab => ?_,
    fun a b ha hb hab => ?_, fun k hk => ?_, ?_⟩
  · simpa using q' (WRel.gInv k hk)
  · simpa using q' (WRel.invG k hk)
  · simpa using q' (WRel.braid k hk)
  · simpa using q' (WRel.farBraid k l hk hl hd)
  · simpa using q' (WRel.farGE k l hk hl hd)
  · simpa using q' (WRel.farEE k l hk hl hd)
  · simpa using q' (WRel.affineFar k hk hp)
  · simpa using q' (WRel.affineFarE k hk hp)
  · simpa [Algebra.smul_def] using q' (WRel.ge k hk)
  · simpa [Algebra.smul_def] using q' (WRel.eg k hk)
  · simpa [Algebra.smul_def] using q' (WRel.ege a b ha hb hab)
  · simpa using q' (WRel.gge a b ha hb hab)
  · simpa using q' (WRel.egg a b ha hb hab)
  · have h := q' (WRel.skein k hk)
    simp only [map_sub, map_mul, AlgHom.commutes, map_one] at h
    rw [Algebra.smul_def, map_sub, ← h]; abel
  · simp

theorem solution (S : Type*) [CommRing S] (omega : ℕ → S)
    (rho q : Sˣ) (hcompat : (↑(rho⁻¹) : S) - ↑rho =
      ((↑(q⁻¹) : S) - ↑q) * (omega 0 - 1)) (n : ℕ) :
    let K : Kind S omega := .ordinary rho q hcompat
    ConjugateCommutation n (ag S omega K n) (agi S omega K n) (ae S omega K n) (ay S omega K n) ∧
    (∀ (r : ℕ) (u : Fin r → S), ValidRoots K u →
      ConjugateCommutation n (cg S omega K r u n) (cgi S omega K r u n)
        (ce S omega K r u n) (cy S omega K r u n)) := by
  intro K
  cases n with
  | zero =>
    refine ⟨fun i j hi => absurd hi (by omega), fun r u _ i j hi => absurd hi (by omega)⟩
  | succ m =>
    have H : ConjugateCommutation (m+1) (ag S omega K (m+1)) (agi S omega K (m+1))
        (ae S omega K (m+1)) (ay S omega K (m+1)) := g66n2_cc (g66n2_wR S omega rho q (m+1))
    refine ⟨H, fun r u _ => ?_⟩
    exact g66n2_cc_map (toCycl S omega K r u (m+1)) (m+1) _ _ _ _ H
