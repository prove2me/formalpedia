-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.local_separation_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:38:11.090057+00:00
-- url     : https://prove2.me/submissions/df348bd8-8088-43d2-afda-6a43e114c89c

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section SeparatedDefinitions

variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]

variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}

variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

theorem g71g4_dom_refl (t : CellTableau Shape T) : tabDominates t t := by
  obtain ⟨l, s⟩ := t
  exact Or.inr ⟨l, s, s, rfl, rfl, le_rfl⟩

theorem g71g4_dom_trans {a b c : CellTableau Shape T} (h1 : tabDominates a b)
    (h2 : tabDominates b c) : tabDominates a c := by
  rcases h1 with h1 | ⟨l, s, t, rfl, rfl, h1⟩
  · rcases h2 with h2 | ⟨l', s', t', rfl, rfl, h2⟩
    · exact Or.inl (lt_trans h2 h1)
    · exact Or.inl h1
  · rcases h2 with h2 | ⟨l', s', t', h3, rfl, h2⟩
    · exact Or.inl h2
    · cases h3
      exact Or.inr ⟨l, s, t', rfl, rfl, le_trans h2 h1⟩

theorem g71g4_dom_antisymm {a b : CellTableau Shape T} (h1 : tabDominates a b)
    (h2 : tabDominates b a) : a = b := by
  rcases h1 with h1 | ⟨l, s, t, rfl, rfl, h1⟩
  · rcases h2 with h2 | ⟨l', s', t', rfl, rfl, h2⟩
    · exact absurd (lt_trans h1 h2) (lt_irrefl _)
    · exact absurd h1 (lt_irrefl _)
  · rcases h2 with h2 | ⟨l', s', t', h3, h4, h2⟩
    · exact absurd h2 (lt_irrefl _)
    · cases h3; cases h4
      rw [le_antisymm h1 h2]

variable (D) in
def g71g4_X (Q : CellTableau Shape T → Prop) : Submodule K A :=
  Submodule.span K {a | ∃ (m : Shape) (x y : T m), Q ⟨m, y⟩ ∧ a = D.basis ⟨m, (x, y)⟩}

theorem g71g4_X_mono {Q Q' : CellTableau Shape T → Prop} (h : ∀ t, Q t → Q' t) :
    g71g4_X D Q ≤ g71g4_X D Q' := by
  apply Submodule.span_mono
  rintro _ ⟨m, x, y, hq, rfl⟩
  exact ⟨m, x, y, h _ hq, rfl⟩

theorem g71g4_X_gen {Q : CellTableau Shape T → Prop} {m : Shape} (x y : T m) (h : Q ⟨m, y⟩) :
    D.basis ⟨m, (x, y)⟩ ∈ g71g4_X D Q :=
  Submodule.subset_span ⟨m, x, y, h, rfl⟩

theorem g71g4_X_coef {Q : CellTableau Shape T → Prop} {m : Shape} (x y : T m) (h : ¬ Q ⟨m, y⟩)
    (w : A) (hw : w ∈ g71g4_X D Q) : D.basis.repr w ⟨m, (x, y)⟩ = 0 := by
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m', x', y', hq, rfl⟩ := hz
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg]
    intro he
    cases he
    exact h hq
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

theorem g71g4_higher_le (m : Shape) :
    higherSpan (R := K) D.basis m ≤ g71g4_X D (fun t => m < t.1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨m', s', t', hlt, rfl⟩
  exact g71g4_X_gen s' t' hlt

theorem g71g4_star_higher (m : Shape) (w : A) (hw : w ∈ higherSpan (R := K) D.basis m) :
    D.star w ∈ higherSpan (R := K) D.basis m := by
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m', s', t', hlt, rfl⟩ := hz
    rw [D.star_basis]
    exact Submodule.subset_span ⟨m', t', s', hlt, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem g71g4_mul_right {Q : CellTableau Shape T → Prop} {N : Submodule K A} {z : A}
    (h : ∀ (m : Shape) (x y : T m), Q ⟨m, y⟩ → D.basis ⟨m, (x, y)⟩ * z ∈ N) :
    ∀ w ∈ g71g4_X D Q, w * z ∈ N := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨m, x, y, hq, rfl⟩ := ha
    exact h m x y hq
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact N.add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact N.smul_mem c ha

theorem g71g4_mul_left {Q : CellTableau Shape T → Prop} {N : Submodule K A} {z : A}
    (h : ∀ (m : Shape) (x y : T m), Q ⟨m, y⟩ → z * D.basis ⟨m, (x, y)⟩ ∈ N) :
    ∀ w ∈ g71g4_X D Q, z * w ∈ N := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨m, x, y, hq, rfl⟩ := ha
    exact h m x y hq
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact N.add_mem ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact N.smul_mem c ha

/-- Up-closed predicates give left ideals. -/
theorem g71g4_left_ideal {Q : CellTableau Shape T → Prop}
    (hQ : ∀ a b, Q a → tabDominates b a → Q b) (b : A) :
    ∀ w ∈ g71g4_X D Q, b * w ∈ g71g4_X D Q := by
  apply g71g4_mul_left
  intro m x y hq
  obtain ⟨r, hr⟩ := D.multiplication m x (D.star b)
  have h := g71g4_star_higher m _ (hr y)
  rw [map_sub, D.star_mul, D.star_involutive b, D.star_basis, map_sum] at h
  simp only [map_smul, D.star_basis] at h
  have hH : higherSpan (R := K) D.basis m ≤ g71g4_X D Q :=
    (g71g4_higher_le m).trans (g71g4_X_mono (fun t ht => hQ ⟨m, y⟩ t hq (Or.inl ht)))
  have := Submodule.add_mem _ (hH h) (Submodule.sum_mem _ (t := Finset.univ) (fun v _ =>
    Submodule.smul_mem _ (r v) (g71g4_X_gen (Q := Q) v y hq)))
  rwa [sub_add_cancel] at this

/-- Triangularity of right multiplication by L. -/
theorem g71g4_tri (J : JMFamily D M) (m : Shape) (x y : T m) (i : Fin M) :
    D.basis ⟨m, (x, y)⟩ * J.L i - J.content ⟨m, y⟩ i • D.basis ⟨m, (x, y)⟩ ∈
      g71g4_X D (fun t => tabDominates t ⟨m, y⟩ ∧ t ≠ ⟨m, y⟩) := by
  obtain ⟨r, hr⟩ := J.triangular m y i
  have h := (g71g4_higher_le m).trans
    (g71g4_X_mono (Q' := fun t => tabDominates t ⟨m, y⟩ ∧ t ≠ ⟨m, y⟩)
      (fun t ht => ⟨Or.inl ht, fun he => by rw [he] at ht; exact lt_irrefl _ ht⟩)) (hr x)
  have hs : ∑ v ∈ Finset.univ.filter (fun v : T m => y < v), r v • D.basis ⟨m, (x, v)⟩ ∈
      g71g4_X D (fun t => tabDominates t ⟨m, y⟩ ∧ t ≠ ⟨m, y⟩) := by
    apply Submodule.sum_mem
    intro v hv
    have hyv : y < v := (Finset.mem_filter.mp hv).2
    apply Submodule.smul_mem
    apply g71g4_X_gen
    refine ⟨Or.inr ⟨m, v, y, rfl, rfl, le_of_lt hyv⟩, fun he => ?_⟩
    cases he
    exact lt_irrefl _ hyv
  have := Submodule.add_mem _ h hs
  rwa [sub_add_cancel] at this

theorem g71g4_rmul_alg (w : A) (c : K) : w * algebraMap K A c = c • w := by
  rw [← Algebra.commutes, ← Algebra.smul_def]

/-- Up-closed predicates are stable under right multiplication by L. -/
theorem g71g4_right_L (J : JMFamily D M) {Q : CellTableau Shape T → Prop}
    (hQ : ∀ a b, Q a → tabDominates b a → Q b) (i : Fin M) (c : K) :
    ∀ w ∈ g71g4_X D Q, w * (J.L i - algebraMap K A c) ∈ g71g4_X D Q := by
  apply g71g4_mul_right
  intro m x y hq
  have h := g71g4_X_mono (Q' := Q) (fun t ht => hQ _ t hq ht.1) (g71g4_tri J m x y i)
  rw [mul_sub, g71g4_rmul_alg]
  have := Submodule.add_mem _ h (Submodule.smul_mem _ (J.content ⟨m, y⟩ i - c)
    (g71g4_X_gen (D := D) (Q := Q) x y hq))
  convert this using 1
  rw [sub_smul]; abel

/-- Peeling a minimal element. -/
theorem g71g4_peel (J : JMFamily D M) (Dm : CellTableau Shape T → Prop)
    (hDm : ∀ a b, tabDominates b a → Dm b → Dm a)
    (P : Finset (CellTableau Shape T)) (t : CellTableau Shape T) (htP : t ∈ P)
    (hup : ∀ a ∈ P, ∀ b, tabDominates b a → Dm b → b ∈ P)
    (hmin : ∀ b ∈ P, tabDominates t b → b = t) (i : Fin M) :
    ∀ w ∈ g71g4_X D (fun u => u ∈ P ∨ ¬ Dm u),
      w * (J.L i - algebraMap K A (J.content t i)) ∈ g71g4_X D (fun u => u ∈ P.erase t ∨ ¬ Dm u) := by
  apply g71g4_mul_right
  intro m x y hq
  have h := g71g4_X_mono (Q' := fun u => u ∈ P.erase t ∨ ¬ Dm u) (fun t' ht' => by
    by_cases hd : Dm t'
    · left
      rcases hq with hq | hq
      · refine Finset.mem_erase.mpr ⟨fun he => ?_, hup _ hq t' ht'.1 hd⟩
        rw [he] at ht'
        exact ht'.2 (hmin _ hq ht'.1).symm
      · exact absurd (hDm _ _ ht'.1 hd) hq
    · exact Or.inr hd) (g71g4_tri J m x y i)
  rw [mul_sub, g71g4_rmul_alg]
  by_cases hy : (⟨m, y⟩ : CellTableau Shape T) = t
  · have hc : J.content t i = J.content ⟨m, y⟩ i := by rw [hy]
    rw [hc]; exact h
  · have := Submodule.add_mem _ h (Submodule.smul_mem _ (J.content ⟨m, y⟩ i - J.content t i)
      (g71g4_X_gen (D := D) (Q := fun u => u ∈ P.erase t ∨ ¬ Dm u) x y
        (hq.imp (fun h => Finset.mem_erase.mpr ⟨hy, h⟩) id)))
    convert this using 1
    rw [sub_smul]; abel

theorem g71g4_prod (l : Shape) (s x : T l) (hg : gramEntry D l s x = 0) :
    D.basis ⟨l, (s, s)⟩ * D.basis ⟨l, (x, s)⟩ ∈ higherSpan (R := K) D.basis l := by
  have hcoef : ∀ w ∈ higherSpan (R := K) D.basis l, ∀ a b : T l,
      D.basis.repr w ⟨l, (a, b)⟩ = 0 := by
    intro w hw a b
    exact g71g4_X_coef (Q := fun t => l < t.1) a b (lt_irrefl l) w (g71g4_higher_le l hw)
  obtain ⟨r, hr⟩ := D.multiplication l s (D.basis ⟨l, (x, s)⟩)
  obtain ⟨r', hr'⟩ := D.multiplication l x (D.basis ⟨l, (s, s)⟩)
  have h1 := hr s
  have h2 := hr' s
  have h3 := g71g4_star_higher l _ h1
  rw [map_sub, D.star_mul, D.star_basis, D.star_basis, map_sum] at h3
  simp only [map_smul, D.star_basis] at h3
  have h4 := Submodule.sub_mem _ h2 h3
  have hrv : ∀ v, v ≠ s → r v = 0 := by
    intro v hv
    have := hcoef _ h4 v s
    simp only [map_sub, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_sub, Pi.sub_apply,
      Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
      Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and, smul_eq_mul] at this
    simpa [Ne.symm hv] using this
  have hrs : r s = 0 := by
    have := hcoef _ h1 s s
    simp only [map_sub, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_sub, Pi.sub_apply,
      Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
      Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and, smul_eq_mul] at this
    have hg' : gramEntry D l s x = D.basis.repr (D.basis ⟨l, (s, s)⟩ * D.basis ⟨l, (x, s)⟩)
      ⟨l, (s, s)⟩ := rfl
    rw [← hg', hg] at this
    simpa using this
  have hz : ∑ v : T l, r v • D.basis ⟨l, (s, v)⟩ = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv : v = s
    · rw [hv, hrs, zero_smul]
    · rw [hrv v hv, zero_smul]
  rwa [hz, sub_zero] at h1

/-- Proposition 2.7, PDF p.4. Keep the LOCAL comparable-pair hypothesis at s.
Nonzero form is equivalent to the radical quotient D(lambda) being nonzero. -/
theorem solution (J : JMFamily D M) (l : Shape) (s : T l)
    (hsep : ∀ t : CellTableau Shape T, tabDominates ⟨l, s⟩ t → ⟨l, s⟩ ≠ t →
      ∃ i, J.content t i ≠ J.content ⟨l, s⟩ i) :
    ∃ v w : T l → K, cellForm D l v w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hg : ∀ x : T l, gramEntry D l s x = 0 := by
    intro x
    have := hcon (fun t => if t = s then 1 else 0) (fun u => if u = x then 1 else 0)
    simpa [cellForm] using this
  set ls : CellTableau Shape T := ⟨l, s⟩ with hls
  let Dm : CellTableau Shape T → Prop := fun t => tabDominates ls t
  have hDm : ∀ a b, tabDominates b a → Dm b → Dm a := fun a b h1 h2 => g71g4_dom_trans h2 h1
  have hnDm : ∀ a b, ¬ Dm a → tabDominates b a → ¬ Dm b := fun a b h1 h2 h3 => h1 (hDm a b h2 h3)
  set U := g71g4_X D (fun t => ¬ Dm t) with hU
  set ass := D.basis ⟨l, (s, s)⟩ with hass
  have hUleft : ∀ b, ∀ w ∈ U, b * w ∈ U := g71g4_left_ideal hnDm
  have hUL : ∀ i c, ∀ w ∈ U, w * (J.L i - algebraMap K A c) ∈ U := g71g4_right_L J hnDm
  -- strictly above ls is outside D
  have habove : ∀ i, ass * J.L i - J.content ls i • ass ∈ U := by
    intro i
    exact g71g4_X_mono (fun t ht hd => ht.2 (g71g4_dom_antisymm ht.1 hd)) (g71g4_tri J l s s i)
  have claim : ∀ n (P : Finset (CellTableau Shape T)), P.card = n → ls ∈ P → (∀ a ∈ P, Dm a) →
      (∀ a ∈ P, ∀ b, tabDominates b a → Dm b → b ∈ P) →
      ∃ (E : A) (γ : K), γ ≠ 0 ∧
        (∀ w ∈ g71g4_X D (fun u => u ∈ P ∨ ¬ Dm u), w * E ∈ g71g4_X D (fun u => u = ls ∨ ¬ Dm u)) ∧
        (∀ w ∈ U, w * E ∈ U) ∧ ass * E - γ • ass ∈ U := by
    intro n
    induction n with
    | zero =>
      intro P hP hls _ _
      rw [Finset.card_eq_zero] at hP
      rw [hP] at hls; simp at hls
    | succ n ih =>
      intro P hP hlsP hPD hup
      by_cases hall : ∀ a ∈ P, a = ls
      · refine ⟨1, 1, one_ne_zero, ?_, ?_, ?_⟩
        · intro w hw
          rw [mul_one]
          exact g71g4_X_mono (fun u hu => hu.imp (hall u) id) hw
        · intro w hw; rwa [mul_one]
        · rw [mul_one, one_smul, sub_self]; exact Submodule.zero_mem _
      · push Not at hall
        obtain ⟨b0, hb0, hb0ne⟩ := hall
        let rel : CellTableau Shape T → CellTableau Shape T → Prop :=
          fun a b => tabDominates b a ∧ a ≠ b
        have : IsTrans _ rel := ⟨fun a b c hab hbc =>
          ⟨g71g4_dom_trans hbc.1 hab.1, fun he => by
            rw [he] at hab
            exact hbc.2 (g71g4_dom_antisymm hab.1 hbc.1)⟩⟩
        have : Std.Irrefl rel := ⟨fun a h => h.2 rfl⟩
        obtain ⟨t, htP, htmin⟩ := (Finite.wellFounded_of_trans_of_irrefl rel).has_min
          (P : Set (CellTableau Shape T)) ⟨b0, hb0⟩
        have hmin : ∀ b ∈ P, tabDominates t b → b = t := by
          intro b hb hd
          by_contra hne
          exact htmin b hb ⟨hd, hne⟩
        have htne : t ≠ ls := by
          intro he
          rw [he] at hmin
          exact hb0ne (hmin b0 hb0 (hPD b0 hb0))
        have hP' : (P.erase t).card = n := by rw [Finset.card_erase_of_mem htP, hP]; rfl
        obtain ⟨E', γ', hγ', h1, h2, h3⟩ := ih (P.erase t) hP'
          (Finset.mem_erase.mpr ⟨htne.symm, hlsP⟩)
          (fun a ha => hPD a (Finset.mem_of_mem_erase ha))
          (fun a ha b hb hd => Finset.mem_erase.mpr ⟨fun he => by
            rw [he] at hb
            have := hmin a (Finset.mem_of_mem_erase ha) hb
            exact (Finset.mem_erase.mp ha).1 this, hup a (Finset.mem_of_mem_erase ha) b hb hd⟩)
        obtain ⟨i, hi⟩ := hsep t (hPD t htP) htne.symm
        refine ⟨(J.L i - algebraMap K A (J.content t i)) * E',
          (J.content ls i - J.content t i) * γ', mul_ne_zero (sub_ne_zero.mpr hi.symm) hγ',
          ?_, ?_, ?_⟩
        · intro w hw
          rw [← mul_assoc]
          exact h1 _ (g71g4_peel J Dm hDm P t htP hup hmin i w hw)
        · intro w hw
          rw [← mul_assoc]
          exact h2 _ (hUL i _ w hw)
        · have hu := h2 _ (habove i)
          have hs := Submodule.smul_mem _ (J.content ls i - J.content t i) h3
          have := Submodule.add_mem _ hu hs
          convert this using 1
          rw [← mul_assoc, mul_sub, g71g4_rmul_alg]
          simp only [sub_mul, smul_mul_assoc, smul_sub, mul_smul, sub_smul]
          abel
  obtain ⟨E, γ, hγ, h1, _, h3⟩ := claim _ (Finset.univ.filter Dm) rfl
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g71g4_dom_refl _⟩)
    (fun a ha => (Finset.mem_filter.mp ha).2)
    (fun a _ b _ hd => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
  have hE : E ∈ g71g4_X D (fun u => u = ls ∨ ¬ Dm u) := by
    have h1' := h1 1 (by
      have : (⊤ : Submodule K A) ≤ g71g4_X D (fun u => u ∈ Finset.univ.filter Dm ∨ ¬ Dm u) := by
        rw [← D.basis.span_eq]
        apply Submodule.span_le.mpr
        rintro _ ⟨⟨m, x, y⟩, rfl⟩
        apply g71g4_X_gen
        by_cases hd : Dm ⟨m, y⟩
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
        · exact Or.inr hd
      exact this Submodule.mem_top)
    rwa [one_mul] at h1'
  have hassE : ass * E ∈ U := by
    apply g71g4_mul_left (Q := fun u => u = ls ∨ ¬ Dm u) _ E hE
    intro m x y hq
    rcases hq with hq | hq
    · rw [hls] at hq
      cases hq
      have := g71g4_prod l s x (hg x)
      exact (g71g4_higher_le l).trans (g71g4_X_mono (fun t ht hd => by
        rcases hd with hd | ⟨l', s', t', h5, h6, _⟩
        · exact lt_asymm ht hd
        · rw [h6] at ht; rw [hls] at h5; cases h5; exact lt_irrefl _ ht)) this
    · exact hUleft _ _ (g71g4_X_gen x y hq)
  have hγa : γ • ass ∈ U := by
    have := Submodule.sub_mem _ hassE h3
    rwa [sub_sub_cancel] at this
  have := g71g4_X_coef (D := D) (Q := fun t => ¬ Dm t) s s (not_not.mpr (g71g4_dom_refl _)) _ hγa
  rw [hass, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] at this
  exact hγ this

end SeparatedDefinitions

end
