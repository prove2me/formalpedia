-- Prove2me | solution 1 for StreamSubmod.rounding
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:05:12.316675+00:00
-- url     : https://prove2.me/submissions/b1c6c516-0349-4998-ac45-32c247d604de

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace Aux_StreamSubmod_rounding

open NonmonotoneSubmod.Shared

variable {E : Type} [Fintype E] [DecidableEq E]

lemma F_rec (f : Finset E → ℝ) (x : E → ℝ) (a : E) :
    F f x = x a * F f (Function.update x a 1) + (1 - x a) * F f (Function.update x a 0) := by
  unfold F
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
  have h1 : ∏ i ∈ Finset.univ.erase a,
      (if i ∈ T then Function.update x a 1 i else 1 - Function.update x a 1 i)
      = ∏ i ∈ Finset.univ.erase a, (if i ∈ T then x i else 1 - x i) :=
    Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
  have h0 : ∏ i ∈ Finset.univ.erase a,
      (if i ∈ T then Function.update x a 0 i else 1 - Function.update x a 0 i)
      = ∏ i ∈ Finset.univ.erase a, (if i ∈ T then x i else 1 - x i) :=
    Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
  rw [h1, h0]
  by_cases ha : a ∈ T <;> simp only [ha, ↓reduceIte, Function.update_self] <;> ring

lemma F_indicator (f : Finset E → ℝ) (B : Finset E) :
    F f (fun e => if e ∈ B then 1 else 0) = f B := by
  unfold F
  rw [Finset.sum_eq_single B]
  · rw [Finset.prod_eq_one, mul_one]
    intro i _
    by_cases hi : i ∈ B <;> simp [hi]
  · intro T _ hTB
    have : ∃ i, ¬ (i ∈ T ↔ i ∈ B) := by
      by_contra hcon
      push_neg at hcon
      exact hTB (Finset.ext hcon)
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
    by_cases h1 : i ∈ T <;> by_cases h2 : i ∈ B <;> simp_all
  · intro h
    exact absurd (Finset.mem_univ B) h

noncomputable def u (x : E → ℝ) (i j : E) (b d : ℝ) : E → ℝ := Function.update (Function.update x i b) j d

lemma u_i (x : E → ℝ) (i j : E) (hij : i ≠ j) (b d : ℝ) : u x i j b d i = b := by
  unfold u
  rw [Function.update_of_ne hij, Function.update_self]

lemma u_j (x : E → ℝ) (i j : E) (b d : ℝ) : u x i j b d j = d := by
  unfold u
  rw [Function.update_self]

lemma u_other (x : E → ℝ) (i j : E) (b d : ℝ) (c : E) (hci : c ≠ i) (hcj : c ≠ j) :
    u x i j b d c = x c := by
  unfold u
  rw [Function.update_of_ne hcj, Function.update_of_ne hci]

lemma u_u (x : E → ℝ) (i j : E) (a c b d : ℝ) : u (u x i j a c) i j b d = u x i j b d := by
  funext l
  simp only [u, Function.update_apply]
  by_cases h1 : l = j <;> by_cases h2 : l = i <;> simp [h1, h2]

lemma u_upd_ij (x : E → ℝ) (a : E) (e : ℝ) (i j : E) (b d : ℝ) (hai : a = i ∨ a = j) :
    u (Function.update x a e) i j b d = u x i j b d := by
  funext l
  simp only [u, Function.update_apply]
  rcases hai with h | h <;> by_cases h1 : l = j <;> by_cases h2 : l = i <;> simp [h, h1, h2]

lemma u_upd_comm (x : E → ℝ) (a : E) (e : ℝ) (i j : E) (b d : ℝ) (hai : a ≠ i) (haj : a ≠ j) :
    Function.update (u x i j b d) a e = u (Function.update x a e) i j b d := by
  funext l
  simp only [u, Function.update_apply]
  by_cases h0 : l = a
  · simp [h0, hai, haj]
  · by_cases h1 : l = j <;> by_cases h2 : l = i <;> simp [h0, h1, h2, Ne.symm hai, Ne.symm haj]

lemma sum_update (x : E → ℝ) (i : E) (v : ℝ) :
    ∑ c, Function.update x i v c = ∑ c, x c + (v - x i) := by
  have h : ∀ c, Function.update x i v c = x c + (if c = i then v - x i else 0) := by
    intro c
    by_cases hc : c = i
    · rw [hc, Function.update_self, if_pos rfl]
      ring
    · rw [Function.update_of_ne hc, if_neg hc]
      ring
  rw [Finset.sum_congr rfl (fun c _ => h c), Finset.sum_add_distrib]
  simp

lemma sum_u (x : E → ℝ) (i j : E) (hij : i ≠ j) (b d : ℝ) :
    ∑ c, u x i j b d c = ∑ c, x c + (b - x i) + (d - x j) := by
  unfold u
  rw [sum_update, sum_update, Function.update_of_ne hij.symm]

lemma F_two (f : Finset E → ℝ) (x : E → ℝ) (i j : E) (hij : i ≠ j) :
    F f x = x i * (x j * F f (u x i j 1 1) + (1 - x j) * F f (u x i j 1 0))
      + (1 - x i) * (x j * F f (u x i j 0 1) + (1 - x j) * F f (u x i j 0 0)) := by
  simp only [u]
  rw [F_rec f x i, F_rec f (Function.update x i 1) j, F_rec f (Function.update x i 0) j,
    Function.update_of_ne hij.symm, Function.update_of_ne hij.symm]

lemma F_u_rec (f : Finset E → ℝ) (x : E → ℝ) (i j a : E) (b d : ℝ) (hai : a ≠ i) (haj : a ≠ j) :
    F f (u x i j b d) = x a * F f (u (Function.update x a 1) i j b d)
      + (1 - x a) * F f (u (Function.update x a 0) i j b d) := by
  rw [F_rec f (u x i j b d) a, u_upd_comm x a 1 i j b d hai haj, u_upd_comm x a 0 i j b d hai haj,
    u_other x i j b d a hai haj]

noncomputable def D (f : Finset E → ℝ) (x : E → ℝ) (i j : E) : ℝ :=
  F f (u x i j 1 1) + F f (u x i j 0 0) - F f (u x i j 1 0) - F f (u x i j 0 1)

lemma u_ind (x : E → ℝ) (i j : E) (hij : i ≠ j) (h01 : ∀ c, x c = 0 ∨ x c = 1) (R : Finset E)
    (hR : ∀ c, c ≠ i → c ≠ j → (c ∈ R ↔ x c = 1)) (b d : ℝ) (T : Finset E)
    (hb : b = 0 ∨ b = 1) (hbT : b = 1 ↔ i ∈ T) (hd : d = 0 ∨ d = 1) (hdT : d = 1 ↔ j ∈ T)
    (hT : ∀ c, c ≠ i → c ≠ j → (c ∈ T ↔ c ∈ R)) :
    u x i j b d = fun c => if c ∈ T then 1 else 0 := by
  funext c
  show u x i j b d c = if c ∈ T then 1 else 0
  by_cases hci : c = i
  · rw [hci, u_i x i j hij]
    rcases hb with h | h
    · have : i ∉ T := fun hm => by
        have := hbT.mpr hm
        rw [h] at this
        norm_num at this
      rw [if_neg this, h]
    · rw [if_pos (hbT.mp h), h]
  · by_cases hcj : c = j
    · rw [hcj, u_j]
      rcases hd with h | h
      · have : j ∉ T := fun hm => by
          have := hdT.mpr hm
          rw [h] at this
          norm_num at this
        rw [if_neg this, h]
      · rw [if_pos (hdT.mp h), h]
    · rw [u_other x i j b d c hci hcj]
      rcases h01 c with h | h
      · have : c ∉ T := fun hm => by
          have := (hR c hci hcj).mp ((hT c hci hcj).mp hm)
          rw [h] at this
          norm_num at this
        rw [if_neg this, h]
      · rw [if_pos ((hT c hci hcj).mpr ((hR c hci hcj).mpr h)), h]

lemma cross_le (f : Finset E → ℝ) (hf : Submodular f) (i j : E) (hij : i ≠ j) (W : Finset E) :
    ∀ x : E → ℝ, (∀ c, 0 ≤ x c ∧ x c ≤ 1) → (∀ c, c ∉ W → x c = 0 ∨ x c = 1) →
      D f x i j ≤ 0 := by
  refine Finset.induction_on W ?_ ?_
  · intro x _ h01
    have h01' : ∀ c, x c = 0 ∨ x c = 1 := fun c => h01 c (Finset.notMem_empty c)
    obtain ⟨R, hRdef⟩ : ∃ R : Finset E,
        R = Finset.univ.filter (fun c => x c = 1 ∧ c ≠ i ∧ c ≠ j) := ⟨_, rfl⟩
    have hiR : i ∉ R := by
      rw [hRdef]
      simp
    have hjR : j ∉ R := by
      rw [hRdef]
      simp
    have hR : ∀ c, c ≠ i → c ≠ j → (c ∈ R ↔ x c = 1) := by
      intro c hci hcj
      rw [hRdef]
      simp [hci, hcj]
    have e11 : u x i j 1 1 = fun c => if c ∈ insert i (insert j R) then 1 else 0 :=
      u_ind x i j hij h01' R hR 1 1 _ (Or.inr rfl) (by simp) (Or.inr rfl) (by simp)
        (fun c hci hcj => by simp [hci, hcj])
    have e00 : u x i j 0 0 = fun c => if c ∈ R then 1 else 0 :=
      u_ind x i j hij h01' R hR 0 0 _ (Or.inl rfl) (by simp [hiR]) (Or.inl rfl) (by simp [hjR])
        (fun c _ _ => Iff.rfl)
    have e10 : u x i j 1 0 = fun c => if c ∈ insert i R then 1 else 0 :=
      u_ind x i j hij h01' R hR 1 0 _ (Or.inr rfl) (by simp) (Or.inl rfl)
        (by simp [hjR, hij.symm]) (fun c hci _ => by simp [hci])
    have e01 : u x i j 0 1 = fun c => if c ∈ insert j R then 1 else 0 :=
      u_ind x i j hij h01' R hR 0 1 _ (Or.inl rfl) (by simp [hiR, hij]) (Or.inr rfl)
        (by simp) (fun c _ hcj => by simp [hcj])
    unfold D
    rw [e11, e00, e10, e01, F_indicator, F_indicator, F_indicator, F_indicator]
    have := hf (insert i R) (insert j R)
    have hU : insert i R ∪ insert j R = insert i (insert j R) := by
      ext c
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    have hI : insert i R ∩ insert j R = R := by
      ext c
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨h1 | h1, h2 | h2⟩
        · exact absurd (h1.symm.trans h2) hij
        · exact h2
        · exact h1
        · exact h1
      · intro hc
        exact ⟨Or.inr hc, Or.inr hc⟩
    rw [hU, hI] at this
    linarith
  · intro a W ha ih x hx h01
    have hcube : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∀ c, 0 ≤ Function.update x a v c ∧
        Function.update x a v c ≤ 1 := by
      intro v hv0 hv1 c
      by_cases hc : c = a
      · rw [hc, Function.update_self]
        exact ⟨hv0, hv1⟩
      · rw [Function.update_of_ne hc]
        exact hx c
    have hW : ∀ v : ℝ, (v = 0 ∨ v = 1) → ∀ c, c ∉ W →
        Function.update x a v c = 0 ∨ Function.update x a v c = 1 := by
      intro v hv c hc
      by_cases hca : c = a
      · rw [hca, Function.update_self]
        exact hv
      · rw [Function.update_of_ne hca]
        exact h01 c (fun h => (Finset.mem_insert.mp h).elim hca hc)
    by_cases hai : a = i ∨ a = j
    · have hD : D f (Function.update x a 0) i j = D f x i j := by
        unfold D
        rw [u_upd_ij x a 0 i j 1 1 hai, u_upd_ij x a 0 i j 0 0 hai, u_upd_ij x a 0 i j 1 0 hai,
          u_upd_ij x a 0 i j 0 1 hai]
      rw [← hD]
      exact ih _ (hcube 0 le_rfl zero_le_one) (hW 0 (Or.inl rfl))
    · push_neg at hai
      have hrecD : D f x i j = x a * D f (Function.update x a 1) i j
          + (1 - x a) * D f (Function.update x a 0) i j := by
        unfold D
        rw [F_u_rec f x i j a 1 1 hai.1 hai.2, F_u_rec f x i j a 0 0 hai.1 hai.2,
          F_u_rec f x i j a 1 0 hai.1 hai.2, F_u_rec f x i j a 0 1 hai.1 hai.2]
        ring
      have h1 := ih _ (hcube 1 zero_le_one le_rfl) (hW 1 (Or.inr rfl))
      have h0 := ih _ (hcube 0 le_rfl zero_le_one) (hW 0 (Or.inl rfl))
      rw [hrecD]
      have m1 := mul_le_mul_of_nonneg_left h1 (hx a).1
      have m0 := mul_le_mul_of_nonneg_left h0 (by linarith [(hx a).2] : (0 : ℝ) ≤ 1 - x a)
      linarith

noncomputable def G (a11 a10 a01 a00 xi xj s : ℝ) : ℝ :=
  (xi + s) * ((xj - s) * a11 + (1 - (xj - s)) * a10)
    + (1 - (xi + s)) * ((xj - s) * a01 + (1 - (xj - s)) * a00)

lemma G_quad (a11 a10 a01 a00 xi xj s : ℝ) :
    G a11 a10 a01 a00 xi xj s = G a11 a10 a01 a00 xi xj 0
      + s * ((xj - xi) * a11 + (xi + 1 - xj) * a10 - (1 - xi + xj) * a01 + (xj - xi) * a00)
      + s ^ 2 * (a10 + a01 - a11 - a00) := by
  unfold G
  ring

lemma quad_aux (g0 g1 g2 s1 s2 B C : ℝ) (hC : 0 ≤ C) (hs1 : s1 < 0) (hs2 : 0 < s2)
    (h1 : g1 = g0 + s1 * B + s1 ^ 2 * C) (h2 : g2 = g0 + s2 * B + s2 ^ 2 * C) :
    g0 ≤ g1 ∨ g0 ≤ g2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨k1, k2⟩ := hcon
  have p1 : s2 * (s1 * B + s1 ^ 2 * C) < 0 := mul_neg_of_pos_of_neg hs2 (by linarith)
  have p2 : (-s1) * (s2 * B + s2 ^ 2 * C) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have p3 : 0 ≤ s1 * s2 * (s1 - s2) * C :=
    mul_nonneg (le_of_lt (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hs1 hs2) (by linarith))) hC
  have e : s2 * (s1 * B + s1 ^ 2 * C) + (-s1) * (s2 * B + s2 ^ 2 * C)
      = s1 * s2 * (s1 - s2) * C := by ring
  linarith

lemma G_max (a11 a10 a01 a00 xi xj s1 s2 : ℝ) (hC : a11 + a00 ≤ a10 + a01) (hs1 : s1 < 0)
    (hs2 : 0 < s2) :
    G a11 a10 a01 a00 xi xj 0 ≤ G a11 a10 a01 a00 xi xj s1 ∨
      G a11 a10 a01 a00 xi xj 0 ≤ G a11 a10 a01 a00 xi xj s2 :=
  quad_aux _ _ _ s1 s2 _ _ (by linarith) hs1 hs2 (G_quad a11 a10 a01 a00 xi xj s1)
    (G_quad a11 a10 a01 a00 xi xj s2)

lemma F_move (f : Finset E → ℝ) (x : E → ℝ) (i j : E) (hij : i ≠ j) (s : ℝ) :
    F f (u x i j (x i + s) (x j - s)) = G (F f (u x i j 1 1)) (F f (u x i j 1 0))
      (F f (u x i j 0 1)) (F f (u x i j 0 0)) (x i) (x j) s := by
  unfold G
  rw [F_two f _ i j hij, u_i x i j hij, u_j, u_u, u_u, u_u, u_u]

noncomputable def Fr (x : E → ℝ) : Finset E := Finset.univ.filter (fun c => 0 < x c ∧ x c < 1)

lemma mem_Fr (x : E → ℝ) (c : E) : c ∈ Fr x ↔ 0 < x c ∧ x c < 1 := by
  simp [Fr]

lemma integral_case (f : Finset E → ℝ) (k : ℕ) (x : E → ℝ) (h01 : ∀ c, x c = 0 ∨ x c = 1)
    (hsum : ∑ c, x c < (k : ℝ) + 1) :
    ∃ A : Finset E, (∀ e ∈ A, x e = 1) ∧ A.card ≤ k ∧ F f x = f A := by
  obtain ⟨A, hA⟩ : ∃ A : Finset E, A = Finset.univ.filter (fun c => x c = 1) := ⟨_, rfl⟩
  have hx : x = fun c => if c ∈ A then 1 else 0 := by
    funext c
    rcases h01 c with h | h <;> simp [hA, h]
  refine ⟨A, ?_, ?_, ?_⟩
  · intro e he
    rw [hA] at he
    exact (Finset.mem_filter.mp he).2
  · have hs : ∑ c, x c = (A.card : ℝ) := by
      rw [hx]
      simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hs] at hsum
    have : A.card < k + 1 := by exact_mod_cast hsum
    omega
  · rw [hx]
    exact F_indicator f A

lemma move_ok (x : E → ℝ) (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) (i j : E) (hij : i ≠ j)
    (hi : 0 < x i ∧ x i < 1) (hj : 0 < x j ∧ x j < 1) (s : ℝ)
    (hs1 : -min (x i) (1 - x j) ≤ s) (hs2 : s ≤ min (1 - x i) (x j)) :
    (∀ c, 0 ≤ u x i j (x i + s) (x j - s) c ∧ u x i j (x i + s) (x j - s) c ≤ 1) ∧
    ∑ c, u x i j (x i + s) (x j - s) c = ∑ c, x c ∧
    (∀ e, 0 < u x i j (x i + s) (x j - s) e → 0 < x e) ∧
    Fr (u x i j (x i + s) (x j - s)) ⊆ Fr x := by
  have m1 := min_le_left (x i) (1 - x j)
  have m2 := min_le_right (x i) (1 - x j)
  have m3 := min_le_left (1 - x i) (x j)
  have m4 := min_le_right (1 - x i) (x j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    by_cases hci : c = i
    · rw [hci, u_i x i j hij]
      constructor <;> linarith
    · by_cases hcj : c = j
      · rw [hcj, u_j]
        constructor <;> linarith
      · rw [u_other x i j _ _ c hci hcj]
        exact hx c
  · rw [sum_u x i j hij]
    ring
  · intro e he
    by_cases hei : e = i
    · rw [hei]
      exact hi.1
    · by_cases hej : e = j
      · rw [hej]
        exact hj.1
      · rw [u_other x i j _ _ e hei hej] at he
        exact he
  · intro c hc
    rw [mem_Fr] at hc ⊢
    by_cases hci : c = i
    · rw [hci]
      exact hi
    · by_cases hcj : c = j
      · rw [hcj]
        exact hj
      · rw [u_other x i j _ _ c hci hcj] at hc
        exact hc

lemma round_main (f : Finset E → ℝ) (hf : Submodular f) (k : ℕ) (n : ℕ) :
    ∀ x : E → ℝ, (Fr x).card = n → (∀ c, 0 ≤ x c ∧ x c ≤ 1) → ∑ c, x c ≤ (k : ℝ) →
      ∃ A : Finset E, (∀ e ∈ A, 0 < x e) ∧ A.card ≤ k ∧ F f x ≤ f A := by
  refine Nat.strong_induction_on n ?_
  intro n ih x hn hx hsum
  by_cases h2 : ∃ i j, i ≠ j ∧ i ∈ Fr x ∧ j ∈ Fr x
  · obtain ⟨i, j, hij, hi, hj⟩ := h2
    have hiF := hi
    have hjF := hj
    rw [mem_Fr] at hi hj
    obtain ⟨s1, hs1d⟩ : ∃ s1 : ℝ, s1 = -min (x i) (1 - x j) := ⟨_, rfl⟩
    obtain ⟨s2, hs2d⟩ : ∃ s2 : ℝ, s2 = min (1 - x i) (x j) := ⟨_, rfl⟩
    have hs1 : s1 < 0 := by
      rw [hs1d]
      exact neg_neg_of_pos (lt_min hi.1 (by linarith [hj.2]))
    have hs2 : 0 < s2 := by
      rw [hs2d]
      exact lt_min (by linarith [hi.2]) hj.1
    have hle : s1 ≤ s2 := by linarith
    have hcross : F f (u x i j 1 1) + F f (u x i j 0 0) ≤ F f (u x i j 1 0) + F f (u x i j 0 1) := by
      have := cross_le f hf i j hij Finset.univ x hx (fun c hc => absurd (Finset.mem_univ c) hc)
      unfold D at this
      linarith
    have hF0 : F f x = G (F f (u x i j 1 1)) (F f (u x i j 1 0))
        (F f (u x i j 0 1)) (F f (u x i j 0 0)) (x i) (x j) 0 := by
      rw [F_two f x i j hij]
      unfold G
      ring
    have hm1 : i ∉ Fr (u x i j (x i + s1) (x j - s1)) ∨ j ∉ Fr (u x i j (x i + s1) (x j - s1)) := by
      rcases le_total (x i) (1 - x j) with h | h
      · left
        rw [mem_Fr, u_i x i j hij, hs1d, min_eq_left h]
        intro hc
        linarith [hc.1]
      · right
        rw [mem_Fr, u_j, hs1d, min_eq_right h]
        intro hc
        linarith [hc.2]
    have hm2 : i ∉ Fr (u x i j (x i + s2) (x j - s2)) ∨ j ∉ Fr (u x i j (x i + s2) (x j - s2)) := by
      rcases le_total (1 - x i) (x j) with h | h
      · left
        rw [mem_Fr, u_i x i j hij, hs2d, min_eq_left h]
        intro hc
        linarith [hc.2]
      · right
        rw [mem_Fr, u_j, hs2d, min_eq_right h]
        intro hc
        linarith [hc.1]
    have finish : ∀ s : ℝ, s1 ≤ s → s ≤ s2 →
        (i ∉ Fr (u x i j (x i + s) (x j - s)) ∨ j ∉ Fr (u x i j (x i + s) (x j - s))) →
        F f x ≤ F f (u x i j (x i + s) (x j - s)) →
        ∃ A : Finset E, (∀ e ∈ A, 0 < x e) ∧ A.card ≤ k ∧ F f x ≤ f A := by
      intro s hsa hsb hm hFle
      obtain ⟨c1, c2, c3, c4⟩ := move_ok x hx i j hij hi hj s (by rw [← hs1d]; exact hsa)
        (by rw [← hs2d]; exact hsb)
      have hlt : (Fr (u x i j (x i + s) (x j - s))).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset c4]
        rcases hm with h | h
        · exact ⟨i, hiF, h⟩
        · exact ⟨j, hjF, h⟩
      obtain ⟨A, hA1, hA2, hA3⟩ := ih _ hlt _ rfl c1 (by rw [c2]; exact hsum)
      exact ⟨A, fun e he => c3 e (hA1 e he), hA2, le_trans hFle hA3⟩
    rcases G_max _ _ _ _ (x i) (x j) s1 s2 hcross hs1 hs2 with h | h
    · exact finish s1 le_rfl hle hm1 (by rw [hF0, F_move f x i j hij s1]; exact h)
    · exact finish s2 hle le_rfl hm2 (by rw [hF0, F_move f x i j hij s2]; exact h)
  · push_neg at h2
    by_cases h1 : ∃ i, i ∈ Fr x
    · obtain ⟨i, hi⟩ := h1
      have hother : ∀ c, c ≠ i → x c = 0 ∨ x c = 1 := by
        intro c hc
        have hcn : c ∉ Fr x := h2 i c (Ne.symm hc) hi
        rw [mem_Fr] at hcn
        rcases (hx c).1.lt_or_eq with h | h
        · right
          by_contra hne
          exact hcn ⟨h, lt_of_le_of_ne (hx c).2 hne⟩
        · left
          exact h.symm
      rw [mem_Fr] at hi
      have h01 : ∀ v : ℝ, (v = 0 ∨ v = 1) → ∀ c,
          Function.update x i v c = 0 ∨ Function.update x i v c = 1 := by
        intro v hv c
        by_cases hc : c = i
        · rw [hc, Function.update_self]
          exact hv
        · rw [Function.update_of_ne hc]
          exact hother c hc
      have hsum1 : ∑ c, Function.update x i 1 c < (k : ℝ) + 1 := by
        rw [sum_update]
        linarith [hi.1]
      have hsum0 : ∑ c, Function.update x i 0 c < (k : ℝ) + 1 := by
        rw [sum_update]
        linarith [hi.1]
      obtain ⟨A1, hA1, hc1, hF1⟩ := integral_case f k _ (h01 1 (Or.inr rfl)) hsum1
      obtain ⟨A0, hA0, hc0, hF0⟩ := integral_case f k _ (h01 0 (Or.inl rfl)) hsum0
      have hrec := F_rec f x i
      by_cases hcmp : F f (Function.update x i 0) ≤ F f (Function.update x i 1)
      · refine ⟨A1, ?_, hc1, ?_⟩
        · intro e he
          have he1 := hA1 e he
          by_cases hei : e = i
          · rw [hei]
            exact hi.1
          · rw [Function.update_of_ne hei] at he1
            rw [he1]
            norm_num
        · have m := mul_le_mul_of_nonneg_left hcmp (by linarith [hi.2] : (0 : ℝ) ≤ 1 - x i)
          rw [← hF1]
          linarith
      · push_neg at hcmp
        refine ⟨A0, ?_, hc0, ?_⟩
        · intro e he
          have he0 := hA0 e he
          by_cases hei : e = i
          · rw [hei, Function.update_self] at he0
            norm_num at he0
          · rw [Function.update_of_ne hei] at he0
            rw [he0]
            norm_num
        · have m := mul_le_mul_of_nonneg_left hcmp.le hi.1.le
          rw [← hF0]
          linarith
    · push_neg at h1
      have h01 : ∀ c, x c = 0 ∨ x c = 1 := by
        intro c
        have hcn := h1 c
        rw [mem_Fr] at hcn
        rcases (hx c).1.lt_or_eq with h | h
        · right
          by_contra hne
          exact hcn ⟨h, lt_of_le_of_ne (hx c).2 hne⟩
        · left
          exact h.symm
      obtain ⟨A, hA, hc, hF⟩ := integral_case f k x h01 (by linarith)
      refine ⟨A, ?_, hc, le_of_eq hF⟩
      intro e he
      rw [hA e he]
      norm_num

end Aux_StreamSubmod_rounding

open NonmonotoneSubmod.Shared in
theorem solution {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf : Submodular f)
    (k : ℕ) (x : E → ℝ) (hx0 : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e ≤ 1)
    (hxk : ∑ e, x e ≤ (k : ℝ)) :
    ∃ A : Finset E, (∀ e ∈ A, 0 < x e) ∧ A.card ≤ k ∧ F f x ≤ f A :=
  Aux_StreamSubmod_rounding.round_main f hf k _ x rfl (fun c => ⟨hx0 c, hx1 c⟩) hxk
