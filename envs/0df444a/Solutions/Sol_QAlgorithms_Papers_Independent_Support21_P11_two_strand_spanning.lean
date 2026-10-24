-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P11.two_strand_spanning
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:47:55.081991+00:00
-- url     : https://prove2.me/submissions/df5697e2-58d1-4d33-b849-e2d5c9d7d159

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11


namespace X8BMW

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]

structure Rels (ω : ℕ → R) (q : Polynomial R) (r : ℕ) (S E X Y : A) : Prop where
  hr : 1 ≤ r
  ss : S * S = 1
  ee : E * E = ω 0 • E
  xy : X * Y = Y * X
  skl : S * X - Y * S = E - 1
  skr : X * S - S * Y = E - 1
  unw : ∀ a, 0 < a → E * X ^ a * E = ω a • E
  es : E * S = E
  se : S * E = E
  ey : E * (X + Y) = 0
  ye : (X + Y) * E = 0
  qm : q.Monic
  qd : q.natDegree = r
  qx : Polynomial.aeval X q = 0

def Gen (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A] (S E X Y : A) : Prop :=
  ∀ N : Submodule R A, (∀ z ∈ N, S * z ∈ N) → (∀ z ∈ N, E * z ∈ N) → (∀ z ∈ N, X * z ∈ N) →
    (∀ z ∈ N, Y * z ∈ N) → ∀ w, ∀ z ∈ N, w * z ∈ N

section
variable {ω : ℕ → R} {q : Polynomial R} {r : ℕ} {S E X Y : A} (h : Rels ω q r S E X Y)
include h

lemma sX : S * X = Y * S + E - 1 := by
  have := h.skl; rw [sub_eq_iff_eq_add] at this; rw [this]; abel

lemma xS : X * S = S * Y + E - 1 := by
  have := h.skr; rw [sub_eq_iff_eq_add] at this; rw [this]; abel

lemma sY : S * Y = X * S - E + 1 := by rw [xS h]; abel

lemma eY : E * Y = -(E * X) := by
  have := h.ey; rw [mul_add] at this; exact (neg_eq_of_add_eq_zero_right this).symm

lemma yE : Y * E = -(X * E) := by
  have := h.ye; rw [add_mul] at this; exact (neg_eq_of_add_eq_zero_right this).symm

lemma eXe (a : ℕ) : E * X ^ a * E = ω a • E := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [pow_zero, mul_one, h.ee]
  · exact h.unw a ha

lemma cXY (a b : ℕ) : X ^ a * Y ^ b = Y ^ b * X ^ a :=
  (Commute.pow_pow (h.xy : Commute X Y) a b).eq

lemma cYX (b : ℕ) : Y ^ b * X = X * Y ^ b := by
  have := cXY h 1 b; rw [pow_one] at this; exact this.symm

lemma cYXa (a : ℕ) : Y * X ^ a = X ^ a * Y := by
  have := cXY h a 1; rw [pow_one] at this; exact this.symm

lemma yPowE (b : ℕ) : Y ^ b * E = (-1 : R) ^ b • (X ^ b * E) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ Y b, mul_assoc, yE h, mul_neg, ← mul_assoc, cYX h, mul_assoc, ih, mul_smul_comm,
      ← mul_assoc, ← pow_succ', pow_succ (-1 : R), mul_neg_one, neg_smul]

lemma ePowY (b : ℕ) : E * Y ^ b = (-1 : R) ^ b • (E * X ^ b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ Y b, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, ← cYXa h, ← mul_assoc, eY h,
      neg_mul, mul_assoc, ← pow_succ', smul_neg, pow_succ (-1 : R), mul_neg_one, neg_smul]

/-- reduction of powers of X via the cyclotomic polynomial -/
lemma xPow_eq (a : ℕ) : ∃ c : ℕ → R, X ^ a = ∑ i ∈ Finset.range r, c i • X ^ i := by
  have hq1 : q ≠ 1 := by
    intro h1; have := h.qd; rw [h1, Polynomial.natDegree_one] at this; have := h.hr; omega
  have hlt := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ a) h.qm hq1
  rw [h.qd] at hlt
  refine ⟨fun i => (Polynomial.X ^ a %ₘ q).coeff i, ?_⟩
  rw [← Polynomial.aeval_eq_sum_range' hlt]
  have := Polynomial.modByMonic_add_div (Polynomial.X ^ a) q
  have e : (Polynomial.aeval X) (Polynomial.X ^ a : Polynomial R) = X ^ a := by simp
  rw [← e]; conv_lhs => rw [← this]
  rw [map_add, map_mul, h.qx, zero_mul, add_zero]

lemma redL (N : Submodule R A) (Z : A) (hZ : ∀ j < r, X ^ j * Z ∈ N) (a : ℕ) :
    X ^ a * Z ∈ N := by
  obtain ⟨c, hc⟩ := xPow_eq h a
  rw [hc, Finset.sum_mul]
  exact N.sum_mem fun i hi => by
    rw [smul_mul_assoc]; exact N.smul_mem _ (hZ i (Finset.mem_range.1 hi))

lemma redR (N : Submodule R A) (Z : A) (hZ : ∀ j < r, Z * X ^ j ∈ N) (a : ℕ) :
    Z * X ^ a ∈ N := by
  obtain ⟨c, hc⟩ := xPow_eq h a
  rw [hc, Finset.mul_sum]
  exact N.sum_mem fun i hi => by
    rw [mul_smul_comm]; exact N.smul_mem _ (hZ i (Finset.mem_range.1 hi))

/-! ### Part 1: the left ideal -/

abbrev J (r : ℕ) (E X : A) : Submodule R A :=
  Submodule.span R (Set.range fun a : Fin r => X ^ (a : ℕ) * E)

omit h in
lemma left_closed (N : Submodule R A) (g : A) (hg : ∀ z ∈ Submodule.span R (∅ : Set A) ⊔ N, g * z ∈ N) :
    ∀ z ∈ N, g * z ∈ N := fun z hz => hg z (Submodule.mem_sup_right hz)

omit h in
/-- closure of a span under left multiplication, checked on generators -/
lemma span_left (s : Set A) (g : A) (N : Submodule R A) (hs : ∀ z ∈ s, g * z ∈ N) :
    ∀ z ∈ Submodule.span R s, g * z ∈ N := by
  intro z hz
  have : Submodule.span R s ≤ N.comap (LinearMap.mulLeft R g) :=
    Submodule.span_le.2 fun z hz => hs z hz
  exact this hz

omit h in
lemma span_right (s : Set A) (g : A) (N : Submodule R A) (hs : ∀ z ∈ s, z * g ∈ N) :
    ∀ z ∈ Submodule.span R s, z * g ∈ N := by
  intro z hz
  have : Submodule.span R s ≤ N.comap (LinearMap.mulRight R g) :=
    Submodule.span_le.2 fun z hz => hs z hz
  exact this hz

lemma J_mem (a : ℕ) : X ^ a * E ∈ J (R := R) r E X :=
  redL h _ E (fun j hj => Submodule.subset_span (Set.mem_range.2 ⟨⟨j, hj⟩, rfl⟩)) a

lemma J_X : ∀ z ∈ J (R := R) r E X, X * z ∈ J (R := R) r E X := by
  apply span_left
  rintro _ ⟨a, rfl⟩
  rw [← mul_assoc, ← pow_succ']; exact J_mem h _

lemma J_Y : ∀ z ∈ J (R := R) r E X, Y * z ∈ J (R := R) r E X := by
  apply span_left
  rintro _ ⟨a, rfl⟩
  rw [← mul_assoc, cYXa h, mul_assoc, yE h, mul_neg, ← mul_assoc, ← pow_succ]
  exact Submodule.neg_mem _ (J_mem h _)

lemma J_E : ∀ z ∈ J (R := R) r E X, E * z ∈ J (R := R) r E X := by
  apply span_left
  rintro _ ⟨a, rfl⟩
  rw [← mul_assoc, eXe h]
  exact Submodule.smul_mem _ _ (by simpa using J_mem h 0)

lemma J_S : ∀ z ∈ J (R := R) r E X, S * z ∈ J (R := R) r E X := by
  apply span_left
  rintro _ ⟨⟨a, ha⟩, rfl⟩
  dsimp only
  clear ha
  induction a with
  | zero => rw [pow_zero, one_mul, h.se]; simpa using J_mem h 0
  | succ a ih =>
    rw [pow_succ', mul_assoc, ← mul_assoc, sX h]
    have e1 : (Y * S + E - 1) * (X ^ a * E) =
        Y * (S * (X ^ a * E)) + E * (X ^ a * E) - X ^ a * E := by noncomm_ring
    rw [e1]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (J_Y h _ ih)
      (J_E h _ (J_mem h a))) (J_mem h a)


theorem part1 (gen : Gen R S E X Y) :
    Submodule.span R ((fun w => w * E) '' Set.univ) = J (R := R) r E X := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨w, _, rfl⟩
    exact gen _ (J_S h) (J_E h) (J_X h) (J_Y h) w E (by simpa using J_mem h 0)
  · apply Submodule.span_le.2
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨X ^ (a : ℕ), trivial, rfl⟩

/-! ### Part 2: spanning the algebra -/

abbrev Ie (E X : A) : Submodule R A := Submodule.span R {z | ∃ a b : ℕ, z = X ^ a * E * X ^ b}
abbrev Ie0 (E X : A) : Submodule R A := Submodule.span R {z | ∃ c : ℕ, z = E * X ^ c}
abbrev U (j : ℕ) (S E X Y : A) : Submodule R A :=
  Submodule.span R ({z | ∃ a b : ℕ, a + b < j ∧ (z = X ^ a * Y ^ b ∨ z = X ^ a * Y ^ b * S)} ∪
    {z | ∃ a b : ℕ, z = X ^ a * E * X ^ b})
abbrev M (S E X Y : A) : Submodule R A :=
  Submodule.span R ({z | ∃ a b : ℕ, z = X ^ a * Y ^ b ∨ z = X ^ a * Y ^ b * S} ∪
    {z | ∃ a b : ℕ, z = X ^ a * E * X ^ b})

omit h in
lemma Ie0_le : Ie0 (R := R) E X ≤ Ie (R := R) E X := by
  apply Submodule.span_le.2
  rintro _ ⟨c, rfl⟩
  exact Submodule.subset_span ⟨0, c, by simp⟩

lemma Ie0_Y : ∀ z ∈ Ie0 (R := R) E X, z * Y ∈ Ie0 (R := R) E X := by
  apply span_right
  rintro _ ⟨c, rfl⟩
  rw [mul_assoc, ← cYXa h, ← mul_assoc, eY h, neg_mul, mul_assoc, ← pow_succ']
  exact Submodule.neg_mem _ (Submodule.subset_span ⟨c + 1, rfl⟩)

lemma EXS (m : ℕ) : E * X ^ m * S ∈ Ie0 (R := R) E X := by
  induction m with
  | zero => rw [pow_zero, mul_one, h.es]; exact Submodule.subset_span ⟨0, by simp⟩
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, mul_assoc, xS h]
    have e1 : E * X ^ m * (S * Y + E - 1) = E * X ^ m * S * Y + E * X ^ m * E - E * X ^ m := by
      noncomm_ring
    rw [e1, eXe h]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (Ie0_Y h _ ih)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)))
      (Submodule.subset_span ⟨m, rfl⟩)

omit h in
lemma Ie_X : ∀ z ∈ Ie (R := R) E X, X * z ∈ Ie (R := R) E X := by
  apply span_left
  rintro _ ⟨a, b, rfl⟩
  exact Submodule.subset_span ⟨a + 1, b, by simp only [pow_succ', mul_assoc]⟩

omit h in
lemma Ie_Xpow (a : ℕ) : ∀ z ∈ Ie (R := R) E X, X ^ a * z ∈ Ie (R := R) E X := by
  induction a with
  | zero => intro z hz; simpa using hz
  | succ a ih => intro z hz; rw [pow_succ', mul_assoc]; exact Ie_X _ (ih z hz)

lemma Ie_Y : ∀ z ∈ Ie (R := R) E X, Y * z ∈ Ie (R := R) E X := by
  apply span_left
  rintro _ ⟨a, b, rfl⟩
  rw [← mul_assoc, ← mul_assoc, cYXa h, mul_assoc (X ^ a), yE h, mul_neg, neg_mul, ← mul_assoc,
    ← pow_succ]
  exact Submodule.neg_mem _ (Submodule.subset_span ⟨a + 1, b, rfl⟩)

lemma Ie_Ypow (c : ℕ) : ∀ z ∈ Ie (R := R) E X, Y ^ c * z ∈ Ie (R := R) E X := by
  induction c with
  | zero => intro z hz; simpa using hz
  | succ c ih => intro z hz; rw [pow_succ', mul_assoc]; exact Ie_Y h _ (ih z hz)

lemma Ie_S : ∀ z ∈ Ie (R := R) E X, z * S ∈ Ie (R := R) E X := by
  apply span_right
  rintro _ ⟨a, b, rfl⟩
  rw [mul_assoc, mul_assoc]
  apply Ie_Xpow
  rw [← mul_assoc]
  exact Ie0_le (EXS h b)

lemma E_gen : ∀ z ∈ ({z | ∃ a b : ℕ, z = X ^ a * Y ^ b ∨ z = X ^ a * Y ^ b * S} ∪
    {z | ∃ a b : ℕ, z = X ^ a * E * X ^ b}), E * z ∈ Ie (R := R) E X := by
  have h1 : ∀ a b : ℕ, E * (X ^ a * Y ^ b) = (-1 : R) ^ b • (E * X ^ (b + a)) := by
    intro a b
    rw [cXY h, ← mul_assoc, ePowY h, smul_mul_assoc, mul_assoc, ← pow_add]
  rintro _ (⟨a, b, rfl | rfl⟩ | ⟨a, b, rfl⟩)
  · rw [h1]; exact Submodule.smul_mem _ _ (Ie0_le (Submodule.subset_span ⟨_, rfl⟩))
  · rw [← mul_assoc, ← mul_assoc, mul_assoc E, h1, smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Ie0_le (EXS h _))
  · rw [← mul_assoc, ← mul_assoc, eXe h, smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Ie0_le (Submodule.subset_span ⟨_, rfl⟩))

lemma S_XZ (N : Submodule R A) (hY : ∀ z ∈ N, Y * z ∈ N) (hE : ∀ z ∈ N, E * z ∈ N) (Z : A)
    (h0 : S * Z ∈ N) (hZ : ∀ a, X ^ a * Z ∈ N) : ∀ a, S * (X ^ a * Z) ∈ N := by
  intro a
  induction a with
  | zero => simpa using h0
  | succ a ih =>
    rw [pow_succ', mul_assoc, ← mul_assoc, sX h]
    have e1 : (Y * S + E - 1) * (X ^ a * Z) =
        Y * (S * (X ^ a * Z)) + E * (X ^ a * Z) - X ^ a * Z := by noncomm_ring
    rw [e1]
    exact N.sub_mem (N.add_mem (hY _ ih) (hE _ (hZ a))) (hZ a)

lemma S_YZ (N : Submodule R A) (hX : ∀ z ∈ N, X * z ∈ N) (hE : ∀ z ∈ N, E * z ∈ N) (Z : A)
    (h0 : S * Z ∈ N) (hZ : ∀ b, Y ^ b * Z ∈ N) : ∀ b, S * (Y ^ b * Z) ∈ N := by
  intro b
  induction b with
  | zero => simpa using h0
  | succ b ih =>
    rw [pow_succ', mul_assoc, ← mul_assoc, sY h]
    have e1 : (X * S - E + 1) * (Y ^ b * Z) =
        X * (S * (Y ^ b * Z)) - E * (Y ^ b * Z) + Y ^ b * Z := by noncomm_ring
    rw [e1]
    exact N.add_mem (N.sub_mem (hX _ ih) (hE _ (hZ b))) (hZ b)

omit h in
lemma Ie_M : Ie (R := R) E X ≤ M (R := R) S E X Y :=
  Submodule.span_mono Set.subset_union_right

omit h in
lemma P_M (a b : ℕ) : X ^ a * Y ^ b ∈ M (R := R) S E X Y :=
  Submodule.subset_span (Or.inl ⟨a, b, Or.inl rfl⟩)

omit h in
lemma Q_M (a b : ℕ) : X ^ a * Y ^ b * S ∈ M (R := R) S E X Y :=
  Submodule.subset_span (Or.inl ⟨a, b, Or.inr rfl⟩)

omit h in
lemma R_M (a b : ℕ) : X ^ a * E * X ^ b ∈ M (R := R) S E X Y :=
  Submodule.subset_span (Or.inr ⟨a, b, rfl⟩)

lemma M_E : ∀ z ∈ M (R := R) S E X Y, E * z ∈ M (R := R) S E X Y :=
  span_left _ _ _ fun z hz => Ie_M (E_gen h z hz)

omit h in
lemma M_X : ∀ z ∈ M (R := R) S E X Y, X * z ∈ M (R := R) S E X Y := by
  apply span_left
  rintro _ (⟨a, b, rfl | rfl⟩ | ⟨a, b, rfl⟩)
  · rw [← mul_assoc, ← pow_succ']; exact P_M _ _
  · rw [← mul_assoc, ← mul_assoc, ← pow_succ']; exact Q_M _ _
  · rw [← mul_assoc, ← mul_assoc, ← pow_succ']; exact R_M _ _

lemma M_Y : ∀ z ∈ M (R := R) S E X Y, Y * z ∈ M (R := R) S E X Y := by
  apply span_left
  rintro _ (⟨a, b, rfl | rfl⟩ | ⟨a, b, rfl⟩)
  · rw [← mul_assoc, cYXa h, mul_assoc, ← pow_succ']; exact P_M _ _
  · rw [← mul_assoc, ← mul_assoc, cYXa h, mul_assoc (X ^ a), ← pow_succ']; exact Q_M _ _
  · exact Ie_M (Ie_Y h _ (Submodule.subset_span ⟨a, b, rfl⟩))

lemma M_S : ∀ z ∈ M (R := R) S E X Y, S * z ∈ M (R := R) S E X Y := by
  apply span_left
  have hS : S * 1 ∈ M (R := R) S E X Y := by simpa using Q_M (R := R) (S := S) (E := E) (X := X) (Y := Y) 0 0
  have hSS : S * S ∈ M (R := R) S E X Y := by rw [h.ss]; simpa using P_M (R := R) (S := S) (E := E) (X := X) (Y := Y) 0 0
  rintro _ (⟨a, b, rfl | rfl⟩ | ⟨a, b, rfl⟩)
  · have := S_XZ h _ (M_Y h) (M_E h) (Y ^ b)
      (by simpa using S_YZ h _ M_X (M_E h) 1 hS (fun b => by simpa using P_M 0 b) b)
      (fun a => P_M a b) a
    exact this
  · rw [mul_assoc]
    exact S_XZ h _ (M_Y h) (M_E h) (Y ^ b * S)
      (S_YZ h _ M_X (M_E h) S hSS (fun b => by simpa using Q_M 0 b) b)
      (fun a => by rw [← mul_assoc]; exact Q_M a b) a
  · rw [mul_assoc]
    exact S_XZ h _ (M_Y h) (M_E h) (E * X ^ b)
      (by rw [← mul_assoc, h.se]; simpa using R_M 0 b)
      (fun a => by rw [← mul_assoc]; exact R_M a b) a

lemma M_top (gen : Gen R S E X Y) (w : A) : w ∈ M (R := R) S E X Y := by
  have := gen _ (M_S h) (M_E h) M_X (M_Y h) w 1 (by simpa using P_M (R := R) (S := S) (E := E) (X := X) (Y := Y) 0 0)
  simpa using this

lemma E_all (gen : Gen R S E X Y) (w : A) : E * w ∈ Ie (R := R) E X :=
  span_left _ _ _ (E_gen h) w (M_top h gen w)


/-! ### the degree filtration U -/

omit h in
lemma U_mono {j k : ℕ} (hjk : j ≤ k) : U (R := R) j S E X Y ≤ U (R := R) k S E X Y := by
  apply Submodule.span_mono
  rintro _ (⟨a, b, hab, hz⟩ | hz)
  · exact Or.inl ⟨a, b, by omega, hz⟩
  · exact Or.inr hz

omit h in
lemma Ie_U (j : ℕ) : Ie (R := R) E X ≤ U (R := R) j S E X Y :=
  Submodule.span_mono Set.subset_union_right

omit h in
lemma P_U {a b j : ℕ} (hab : a + b < j) : X ^ a * Y ^ b ∈ U (R := R) j S E X Y :=
  Submodule.subset_span (Or.inl ⟨a, b, hab, Or.inl rfl⟩)

omit h in
lemma Q_U {a b j : ℕ} (hab : a + b < j) : X ^ a * Y ^ b * S ∈ U (R := R) j S E X Y :=
  Submodule.subset_span (Or.inl ⟨a, b, hab, Or.inr rfl⟩)

omit h in
lemma U_X (j : ℕ) : ∀ z ∈ U (R := R) j S E X Y, X * z ∈ U (R := R) (j + 1) S E X Y := by
  apply span_left
  rintro _ (⟨a, b, hab, rfl | rfl⟩ | ⟨a, b, rfl⟩)
  · rw [← mul_assoc, ← pow_succ']; exact P_U (by omega)
  · rw [← mul_assoc, ← mul_assoc, ← pow_succ']; exact Q_U (by omega)
  · exact Ie_U _ (Ie_X _ (Submodule.subset_span ⟨a, b, rfl⟩))

lemma U_Y (j : ℕ) : ∀ z ∈ U (R := R) j S E X Y, Y * z ∈ U (R := R) (j + 1) S E X Y := by
  apply span_left
  rintro _ (⟨a, b, hab, rfl | rfl⟩ | ⟨a, b, rfl⟩)
  · rw [← mul_assoc, cYXa h, mul_assoc, ← pow_succ']; exact P_U (by omega)
  · rw [← mul_assoc, ← mul_assoc, cYXa h, mul_assoc (X ^ a), ← pow_succ']; exact Q_U (by omega)
  · exact Ie_U _ (Ie_Y h _ (Submodule.subset_span ⟨a, b, rfl⟩))

lemma SY_U (gen : Gen R S E X Y) (b : ℕ) : S * Y ^ b ∈ U (R := R) (b + 1) S E X Y ∧
    S * (Y ^ b * S) ∈ U (R := R) (b + 1) S E X Y := by
  induction b with
  | zero =>
    refine ⟨by simpa using Q_U (R := R) (S := S) (E := E) (X := X) (Y := Y) (a := 0) (b := 0) (j := 1) (by omega), ?_⟩
    rw [pow_zero, one_mul, h.ss]
    simpa using P_U (R := R) (S := S) (E := E) (X := X) (Y := Y) (a := 0) (b := 0) (j := 1) (by omega)
  | succ b ih =>
    have hP : Y ^ b ∈ U (R := R) (b + 1 + 1) S E X Y := by
      simpa using P_U (R := R) (S := S) (E := E) (X := X) (Y := Y) (a := 0) (b := b) (j := b + 1 + 1) (by omega)
    have hQ : Y ^ b * S ∈ U (R := R) (b + 1 + 1) S E X Y := by
      simpa using Q_U (R := R) (S := S) (E := E) (X := X) (Y := Y) (a := 0) (b := b) (j := b + 1 + 1) (by omega)
    constructor
    · rw [pow_succ', ← mul_assoc, sY h]
      have e1 : (X * S - E + 1) * Y ^ b = X * (S * Y ^ b) - E * Y ^ b + Y ^ b := by noncomm_ring
      rw [e1]
      exact Submodule.add_mem _ (Submodule.sub_mem _ (U_X _ _ ih.1)
        (Ie_U _ (E_all h gen _))) hP
    · rw [pow_succ', mul_assoc, ← mul_assoc, sY h]
      have e1 : (X * S - E + 1) * (Y ^ b * S) =
          X * (S * (Y ^ b * S)) - E * (Y ^ b * S) + Y ^ b * S := by noncomm_ring
      rw [e1]
      exact Submodule.add_mem _ (Submodule.sub_mem _ (U_X _ _ ih.2)
        (Ie_U _ (E_all h gen _))) hQ

lemma SXY_U (gen : Gen R S E X Y) (a b : ℕ) : S * (X ^ a * Y ^ b) ∈ U (R := R) (a + b + 1) S E X Y ∧
    S * (X ^ a * (Y ^ b * S)) ∈ U (R := R) (a + b + 1) S E X Y := by
  induction a with
  | zero => simpa using SY_U h gen b
  | succ a ih =>
    have key : ∀ Z : A, S * (X ^ a * Z) ∈ U (R := R) (a + b + 1) S E X Y →
        X ^ a * Z ∈ U (R := R) (a + 1 + b + 1) S E X Y →
        S * (X ^ (a + 1) * Z) ∈ U (R := R) (a + 1 + b + 1) S E X Y := by
      intro Z h1 h2
      rw [pow_succ', mul_assoc, ← mul_assoc, sX h]
      have e1 : (Y * S + E - 1) * (X ^ a * Z) =
          Y * (S * (X ^ a * Z)) + E * (X ^ a * Z) - X ^ a * Z := by noncomm_ring
      rw [e1]
      have h3 := U_Y h _ _ h1
      rw [show a + b + 1 + 1 = a + 1 + b + 1 by omega] at h3
      exact Submodule.sub_mem _ (Submodule.add_mem _ h3 (Ie_U _ (E_all h gen _))) h2
    exact ⟨key _ ih.1 (P_U (by omega)), key _ ih.2 (by rw [← mul_assoc]; exact Q_U (by omega))⟩

lemma S_Ie (gen : Gen R S E X Y) : ∀ z ∈ Ie (R := R) E X, S * z ∈ Ie (R := R) E X := by
  apply span_left
  rintro _ ⟨a, b, rfl⟩
  rw [mul_assoc]
  exact S_XZ h _ (Ie_Y h) (fun z _ => E_all h gen z) (E * X ^ b)
    (by rw [← mul_assoc, h.se]; exact Submodule.subset_span ⟨0, b, by simp⟩)
    (fun a => by rw [← mul_assoc]; exact Submodule.subset_span ⟨a, b, rfl⟩) a

lemma U_S (gen : Gen R S E X Y) (j : ℕ) : ∀ z ∈ U (R := R) j S E X Y, S * z ∈ U (R := R) (j + 1) S E X Y := by
  apply span_left
  rintro _ (⟨a, b, hab, rfl | rfl⟩ | ⟨a, b, rfl⟩)
  · exact U_mono (by omega) (SXY_U h gen a b).1
  · rw [mul_assoc]; exact U_mono (by omega) (SXY_U h gen a b).2
  · exact Ie_U _ (S_Ie h gen _ (Submodule.subset_span ⟨a, b, rfl⟩))

lemma conj_pow (n : ℕ) : (S * X * S) ^ n = S * X ^ n * S := by
  induction n with
  | zero => simp [h.ss]
  | succ n ih =>
    rw [pow_succ, ih]
    have e1 : S * X ^ n * S * (S * X * S) = S * X ^ n * (S * S) * X * S := by noncomm_ring
    rw [e1, h.ss, mul_one, pow_succ]
    simp only [mul_assoc]

lemma conj_aeval (p : Polynomial R) :
    Polynomial.aeval (S * X * S) p = S * Polynomial.aeval X p * S := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conj_pow h, mul_smul_comm, smul_mul_assoc]

lemma SXS : S * X * S = Y + E - S := by
  rw [sX h]
  have e1 : (Y * S + E - 1) * S = Y * (S * S) + E * S - S := by noncomm_ring
  rw [e1, h.ss, h.es, mul_one]

lemma key_pow (gen : Gen R S E X Y) (j : ℕ) : (Y + E - S) ^ j - Y ^ j ∈ U (R := R) j S E X Y := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨t, ht, e0⟩ : ∃ t ∈ U (R := R) j S E X Y, (Y + E - S) ^ j = Y ^ j + t :=
      ⟨_, ih, by abel⟩
    rw [pow_succ', pow_succ', e0]
    have e1 : (Y + E - S) * (Y ^ j + t) - Y * Y ^ j =
        Y * t + E * (Y ^ j + t) - S * Y ^ j - S * t := by noncomm_ring
    rw [e1]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ (U_Y h _ _ ht)
      (Ie_U _ (E_all h gen _))) (SY_U h gen j).1) (U_S h gen _ _ ht)

lemma Yr_U (gen : Gen R S E X Y) : Y ^ r ∈ U (R := R) r S E X Y := by
  have hz : Polynomial.aeval (Y + E - S) q = 0 := by
    rw [← SXS h, conj_aeval h, h.qx, mul_zero, zero_mul]
  rw [Polynomial.aeval_eq_sum_range, h.qd, Finset.sum_range_succ] at hz
  have hc : q.coeff r = 1 := by rw [← h.qd]; exact h.qm
  rw [hc, one_smul] at hz
  have e1 : Y ^ r = -(∑ i ∈ Finset.range r, q.coeff i • (Y + E - S) ^ i) -
      ((Y + E - S) ^ r - Y ^ r) := by
    rw [eq_neg_of_add_eq_zero_left hz]; abel
  rw [e1]
  refine Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_))
    (key_pow h gen r)
  have hi := Finset.mem_range.1 hi
  refine Submodule.smul_mem _ _ ?_
  have : (Y + E - S) ^ i = ((Y + E - S) ^ i - Y ^ i) + X ^ 0 * Y ^ i := by simp
  rw [this]
  exact Submodule.add_mem _ (U_mono hi.le (key_pow h gen i)) (P_U (by omega))

/-! ### final reduction -/

abbrev Nf (r : ℕ) (S E X Y : A) : Submodule R A :=
  Submodule.span R {z | ∃ a b : ℕ, a < r ∧ b < r ∧
    (z = X ^ a * E * X ^ b ∨ z = X ^ a * Y ^ b * S ∨ z = X ^ a * Y ^ b)}

lemma R_N (a b : ℕ) : X ^ a * E * X ^ b ∈ Nf (R := R) r S E X Y := by
  rw [mul_assoc]
  refine redL h _ _ (fun j hj => ?_) a
  rw [← mul_assoc]
  exact redR h _ _ (fun i hi => by apply Submodule.subset_span; exact ⟨j, i, hj, hi, Or.inl rfl⟩) b

lemma Ie_N : Ie (R := R) E X ≤ Nf (R := R) r S E X Y := by
  apply Submodule.span_le.2
  rintro _ ⟨a, b, rfl⟩
  exact R_N h a b

lemma nf (a c a' b' : ℕ) : X ^ a * Y ^ c * (X ^ a' * Y ^ b') = X ^ (a + a') * Y ^ (c + b') := by
  rw [show X ^ a * Y ^ c * (X ^ a' * Y ^ b') = X ^ a * (Y ^ c * X ^ a') * Y ^ b' by
    simp only [mul_assoc], ← cXY h a' c, pow_add, pow_add]
  simp only [mul_assoc]

lemma PQ_N (gen : Gen R S E X Y) (b : ℕ) : ∀ a, X ^ a * Y ^ b ∈ Nf (R := R) r S E X Y ∧
    X ^ a * Y ^ b * S ∈ Nf (R := R) r S E X Y := by
  induction b using Nat.strong_induction_on with
  | _ b IH =>
  intro a
  by_cases hb : b < r
  · constructor
    · exact redL h _ (Y ^ b)
        (fun j hj => by apply Submodule.subset_span; exact ⟨j, b, hj, hb, Or.inr (Or.inr rfl)⟩) a
    · rw [mul_assoc]
      exact redL h _ (Y ^ b * S) (fun j hj => by
        rw [← mul_assoc]; apply Submodule.subset_span; exact ⟨j, b, hj, hb, Or.inr (Or.inl rfl)⟩) a
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + r := ⟨b - r, by omega⟩
    set w := X ^ a * Y ^ c with hw
    let V : Submodule R A := (Nf (R := R) r S E X Y).comap (LinearMap.mulLeft R w) ⊓
      (Nf (R := R) r S E X Y).comap ((LinearMap.mulLeft R w).comp (LinearMap.mulRight R S))
    have hV : U (R := R) r S E X Y ≤ V := by
      apply Submodule.span_le.2
      rintro _ (⟨a', b', hab, rfl | rfl⟩ | ⟨a', b', rfl⟩)
      · refine ⟨?_, ?_⟩
        · rw [SetLike.mem_coe, Submodule.mem_comap]; show w * (X ^ a' * Y ^ b') ∈ _
          rw [hw, nf h]; exact (IH _ (by omega) _).1
        · rw [SetLike.mem_coe, Submodule.mem_comap]; show w * (X ^ a' * Y ^ b' * S) ∈ _
          rw [hw, ← mul_assoc, nf h]; exact (IH _ (by omega) _).2
      · refine ⟨?_, ?_⟩
        · rw [SetLike.mem_coe, Submodule.mem_comap]; show w * (X ^ a' * Y ^ b' * S) ∈ _
          rw [hw, ← mul_assoc, nf h]; exact (IH _ (by omega) _).2
        · rw [SetLike.mem_coe, Submodule.mem_comap]; show w * (X ^ a' * Y ^ b' * S * S) ∈ _
          rw [hw, mul_assoc _ S S, h.ss, mul_one, nf h]; exact (IH _ (by omega) _).1
      · have hz : X ^ a' * E * X ^ b' ∈ Ie (R := R) E X := Submodule.subset_span ⟨a', b', rfl⟩
        refine ⟨?_, ?_⟩
        · rw [SetLike.mem_coe, Submodule.mem_comap]; show w * (X ^ a' * E * X ^ b') ∈ _
          rw [hw, mul_assoc]; exact Ie_N h (Ie_Xpow a _ (Ie_Ypow h c _ hz))
        · rw [SetLike.mem_coe, Submodule.mem_comap]; show w * (X ^ a' * E * X ^ b' * S) ∈ _
          rw [hw, mul_assoc]; exact Ie_N h (Ie_Xpow a _ (Ie_Ypow h c _ (Ie_S h _ hz)))
    have := hV (Yr_U h gen)
    refine ⟨?_, ?_⟩
    · have h1 := Submodule.mem_comap.1 this.1
      change w * Y ^ r ∈ _ at h1
      rwa [hw, mul_assoc, ← pow_add] at h1
    · have h1 := Submodule.mem_comap.1 this.2
      change w * (Y ^ r * S) ∈ _ at h1
      rwa [hw, ← mul_assoc, mul_assoc (X ^ a), ← pow_add] at h1

theorem part2 (gen : Gen R S E X Y) : Nf (R := R) r S E X Y = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have hM : M (R := R) S E X Y ≤ Nf (R := R) r S E X Y := by
    apply Submodule.span_le.2
    rintro _ (⟨a, b, rfl | rfl⟩ | ⟨a, b, rfl⟩)
    · exact (PQ_N h gen b a).1
    · exact (PQ_N h gen b a).2
    · exact R_N h a b
  exact hM (M_top h gen w)

end

end X8BMW


noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11.X8B

open QAlgorithms.Papers.Independent.Renew46.P16

variable (R : Type*) [CommRing R] (omega : ℕ → R) (r : ℕ) (u : Fin r → R)

abbrev W := CyclotomicBMW R omega 2 r u

def φ : FreeAlgebra R (BMWLetter 2) →ₐ[R] W R omega r u :=
  (cyclotomicMap R omega 2 r u).comp (affineBMWQuotientMap R omega 2)

abbrev S : W R omega r u := cyclotomicS R omega 2 r u 0
abbrev E : W R omega r u := cyclotomicE R omega 2 r u 0
abbrev X : W R omega r u := cyclotomicX R omega 2 r u 0
abbrev Y : W R omega r u := cyclotomicX R omega 2 r u 1

lemma φS : φ R omega r u (freeS R 2 0) = S R omega r u := rfl
lemma φE : φ R omega r u (freeE R 2 0) = E R omega r u := rfl
lemma φX : φ R omega r u (freeX R 2 0) = X R omega r u := rfl
lemma φY : φ R omega r u (freeX R 2 1) = Y R omega r u := rfl

lemma rel {a b : FreeAlgebra R (BMWLetter 2)} (h : BMWRel R omega 2 a b) :
    φ R omega r u a = φ R omega r u b := by
  simp only [φ, AlgHom.comp_apply]
  congr 1
  exact RingQuot.mkAlgHom_rel R h

variable {R omega r u}

lemma SS : S R omega r u * S R omega r u = 1 := by
  have := rel R omega r u (BMWRel.involution 0 (by norm_num))
  rw [map_pow, φS, map_one, sq] at this; exact this

lemma EE : E R omega r u * E R omega r u = omega 0 • E R omega r u := by
  have := rel R omega r u (BMWRel.idempotent 0 (by norm_num))
  rw [map_pow, φE, map_mul, AlgHom.commutes, sq, ← Algebra.smul_def] at this; exact this

lemma XY : X R omega r u * Y R omega r u = Y R omega r u * X R omega r u := by
  have := rel R omega r u (BMWRel.xxCommute 0 1 (by norm_num) (by norm_num))
  rw [map_mul, map_mul, φX, φY] at this; exact this

lemma skL : S R omega r u * X R omega r u -
    Y R omega r u * S R omega r u = E R omega r u - 1 := by
  have := rel R omega r u (BMWRel.skeinLeft 0 (by norm_num))
  rw [map_sub, map_sub, map_mul, map_mul, map_one, φS, φE, φX] at this
  have h1 : φ R omega r u (freeX R 2 (0 + 1)) = Y R omega r u := rfl
  rw [h1] at this
  exact this

lemma skR : X R omega r u * S R omega r u -
    S R omega r u * Y R omega r u = E R omega r u - 1 := by
  have := rel R omega r u (BMWRel.skeinRight 0 (by norm_num))
  rw [map_sub, map_sub, map_mul, map_mul, map_one, φS, φE, φX] at this
  have h1 : φ R omega r u (freeX R 2 (0 + 1)) = Y R omega r u := rfl
  rw [h1] at this
  exact this

lemma unwrap (a : ℕ) (ha : 0 < a) :
    E R omega r u * X R omega r u ^ a * E R omega r u = omega a • E R omega r u := by
  have := rel R omega r u (BMWRel.unwrap a ha le_rfl)
  simp only [map_mul, map_pow, AlgHom.commutes] at this
  rw [φE, φX] at this
  rw [this, Algebra.smul_def]

lemma ES : E R omega r u * S R omega r u = E R omega r u := by
  have := rel R omega r u (BMWRel.es 0 (by norm_num))
  rw [map_mul, φS, φE] at this; exact this

lemma SE : S R omega r u * E R omega r u = E R omega r u := by
  have := rel R omega r u (BMWRel.se 0 (by norm_num))
  rw [map_mul, φS, φE] at this; exact this

lemma EY : E R omega r u * (X R omega r u + Y R omega r u) = 0 := by
  have := rel R omega r u (BMWRel.antisymLeft 0 (by norm_num))
  rw [map_mul, map_add, map_zero, φE, φX] at this
  have h1 : φ R omega r u (freeX R 2 (0 + 1)) = Y R omega r u := rfl
  rw [h1] at this
  exact this

lemma YE : (X R omega r u + Y R omega r u) * E R omega r u = 0 := by
  have := rel R omega r u (BMWRel.antisymRight 0 (by norm_num))
  rw [map_mul, map_add, map_zero, φE, φX] at this
  have h1 : φ R omega r u (freeX R 2 (0 + 1)) = Y R omega r u := rfl
  rw [h1] at this
  exact this

/-- the cyclotomic polynomial as a polynomial over R -/
def q (u : Fin r → R) : Polynomial R :=
  ∏ j : Fin r, (Polynomial.X - Polynomial.C (u j))

lemma q_monic : (q u).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)

lemma q_deg [Nontrivial R] : (q u).natDegree = r := by
  unfold q
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)]
  simp

lemma q_X : Polynomial.aeval (X R omega r u) (q u) = 0 := by
  have h : cyclotomicMap R omega 2 r u (cyclotomicPolynomial R omega 2 r u) = 0 := by
    have := RingQuot.mkAlgHom_rel R
      (s := cyclotomicRel R omega 2 r u) (x := cyclotomicPolynomial R omega 2 r u) (y := 0)
      ⟨rfl, rfl⟩
    rw [map_zero] at this; exact this
  rw [← h, q, ← List.prod_ofFn, map_list_prod, cyclotomicPolynomial, map_list_prod]
  congr 1
  simp [List.map_ofFn, Function.comp_def, X]
  rfl

lemma rels [Nontrivial R] (hr : 1 ≤ r) :
    X8BMW.Rels omega (q u) r (S R omega r u) (E R omega r u) (X R omega r u) (Y R omega r u) :=
  ⟨hr, SS, EE, XY, skL, skR, unwrap, ES, SE, EY, YE, q_monic, q_deg, q_X⟩

lemma φ_surj : Function.Surjective (φ R omega r u) := by
  intro w
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective R (cyclotomicRel R omega 2 r u) w
  obtain ⟨f, rfl⟩ := RingQuot.mkAlgHom_surjective R (BMWRel R omega 2) a
  exact ⟨f, rfl⟩

lemma gen : X8BMW.Gen R (S R omega r u) (E R omega r u) (X R omega r u) (Y R omega r u) := by
  intro N hS hE hX hY w
  obtain ⟨f, rfl⟩ := φ_surj (R := R) (omega := omega) (r := r) (u := u) w
  induction f using FreeAlgebra.induction with
  | grade0 c =>
    intro z hz; rw [AlgHom.commutes, ← Algebra.smul_def]; exact N.smul_mem _ hz
  | grade1 x =>
    intro z hz
    cases x with
    | s i =>
      have : φ R omega r u (FreeAlgebra.ι R (BMWLetter.s i)) = S R omega r u := by
        rw [← φS]; simp only [freeS]; rw [dif_pos (by norm_num)]; congr; ext; simp
      rw [this]; exact hS z hz
    | e i =>
      have : φ R omega r u (FreeAlgebra.ι R (BMWLetter.e i)) = E R omega r u := by
        rw [← φE]; simp only [freeE]; rw [dif_pos (by norm_num)]; congr; ext; simp
      rw [this]; exact hE z hz
    | x i =>
      fin_cases i
      · dsimp only
        have : φ R omega r u (FreeAlgebra.ι R (BMWLetter.x ⟨0, by norm_num⟩)) = X R omega r u := by
          rw [← φX]; simp only [freeX]; rw [dif_pos (by norm_num)]
        rw [this]; exact hX z hz
      · dsimp only
        have : φ R omega r u (FreeAlgebra.ι R (BMWLetter.x ⟨1, by norm_num⟩)) = Y R omega r u := by
          rw [← φY]; simp only [freeX]; rw [dif_pos (by norm_num)]
        rw [this]; exact hY z hz
  | mul a b ha hb =>
    intro z hz; rw [map_mul, mul_assoc]; exact ha _ (hb z hz)
  | add a b ha hb =>
    intro z hz; rw [map_add, add_mul]; exact N.add_mem (ha z hz) (hb z hz)

theorem x8_main (hr : 1 ≤ r) :
    leftIdeal R omega r u = Submodule.span R (Set.range (idealFamily R omega r u)) ∧
    Submodule.span R (Set.range (algebraFamily R omega r u)) = ⊤ := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton (W R omega r u) := Module.subsingleton R _
    have hall : ∀ N₁ N₂ : Submodule R (W R omega r u), N₁ = N₂ := fun N₁ N₂ => by
      ext z; rw [Subsingleton.elim z 0]; simp
    exact ⟨hall _ _, hall _ _⟩
  have h := rels (R := R) (omega := omega) (u := u) hr
  refine ⟨X8BMW.part1 h gen, ?_⟩
  rw [eq_top_iff, ← X8BMW.part2 h gen]
  apply Submodule.span_le.2
  rintro _ ⟨a, b, ha, hb, rfl | rfl | rfl⟩
  · exact Submodule.subset_span ⟨(0, ⟨a, ha⟩, ⟨b, hb⟩), by simp [algebraFamily]⟩
  · exact Submodule.subset_span ⟨(1, ⟨a, ha⟩, ⟨b, hb⟩), by simp [algebraFamily]⟩
  · exact Submodule.subset_span ⟨(2, ⟨a, ha⟩, ⟨b, hb⟩), by simp [algebraFamily]⟩

end QAlgorithms.Papers.Independent.Support21.P11.X8B

open QAlgorithms.Papers.Independent.Support21.P11 in
theorem solution (R : Type*) [CommRing R] (omega : ℕ → R)
    (r : ℕ) (u : Fin r → R) (hr : 1 ≤ r) :
    leftIdeal R omega r u = Submodule.span R (Set.range (idealFamily R omega r u)) ∧
    Submodule.span R (Set.range (algebraFamily R omega r u)) = ⊤ :=
  QAlgorithms.Papers.Independent.Support21.P11.X8B.x8_main hr
