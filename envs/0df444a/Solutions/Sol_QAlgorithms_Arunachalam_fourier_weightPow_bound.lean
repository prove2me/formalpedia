-- Prove2me | solution 1 for QAlgorithms.Arunachalam.fourier_weightPow_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:43:03.43098+00:00
-- url     : https://prove2.me/submissions/33b65434-32b8-4336-bcd1-bff3971782cb

import Theorems.Thm_QAlgorithms_Arunachalam_count_basis_sums
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
open scoped BigOperators
open QAlgorithms

private def sg (a : ZMod 2) : ℝ := (-1 : ℝ) ^ a.val

private lemma bits (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a.val = 0 ∨ a.val = 1 := by have := ZMod.val_lt a; omega
  rcases h with h | h
  · exact Or.inl ((ZMod.val_eq_zero a).mp h)
  · exact Or.inr ((ZMod.val_injective 2) (by simpa only [ZMod.val_one_eq_one_mod] using h))

private lemma sg_add (a b : ZMod 2) : sg (a + b) = sg a * sg b := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  rcases bits a with rfl | rfl <;> rcases bits b with rfl | rfl <;>
    norm_num [sg, h, ZMod.val_zero, ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod]

private lemma two_add (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma vec_two_add {n : ℕ} (a : Fin n → ZMod 2) : a + a = 0 := by
  ext i
  exact two_add (a i)

private lemma add_zero_iff {n : ℕ} (a b : Fin n → ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun x => x + b) h
    simpa only [add_assoc, vec_two_add, add_zero, zero_add] using this
  · rintro rfl
    exact vec_two_add a

private lemma char_sum {n : ℕ} (a : Fin n → ZMod 2) :
    (∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x)) = if a = 0 then (2 : ℝ)^n else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [sg]
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra! h
      exact ha (funext h)
    have hai : a i = 1 := by
      exact (bits (a i)).resolve_left hi
    have shift : (∑ x : Fin n → ZMod 2,
        sg (a ⬝ᵥ (x + (Pi.single i 1 : Fin n → ZMod 2)))) =
        ∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x) :=
      Equiv.sum_comp (Equiv.addRight (Pi.single i 1 : Fin n → ZMod 2))
        (fun x : Fin n → ZMod 2 => sg (a ⬝ᵥ x))
    have hs : (∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ (x + Pi.single i 1))) =
        -(∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x)) := by
      simp_rw [dotProduct_add, dotProduct_single, mul_one, hai, sg_add]
      norm_num [sg, ZMod.val_one_eq_one_mod, Finset.sum_neg_distrib]
    rw [hs] at shift
    rw [if_neg ha]
    linarith

private lemma char_orth {n : ℕ} (a b : Fin n → ZMod 2) :
    (∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x) * sg (b ⬝ᵥ x)) =
      if a = b then (2 : ℝ)^n else 0 := by
  simp_rw [← sg_add, ← add_dotProduct]
  rw [char_sum]
  simp only [add_zero_iff]

private abbrev basis {m : ℕ} (a : Fin m) : Fin m → ZMod 2 := Pi.single a 1

private def walkCount {m : ℕ} (l : ℕ) (S : Fin m → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i : Fin l → Fin m => ∑ j, basis (i j) = S).card

private lemma sg_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sg (∑ i ∈ s, f i) = ∏ i ∈ s, sg (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sg]
  | @insert i s hi ih => simp [hi, sg_add, ih]

private lemma sum_sg (m : ℕ) (z : Fin m → ZMod 2) :
    (∑ i, sg (z i)) = (m : ℝ) - 2 * (hammingNorm z : ℝ) := by
  classical
  have h (i : Fin m) : sg (z i) = 1 - 2 * (if z i ≠ 0 then (1:ℝ) else 0) := by
    rcases bits (z i) with h | h <;> norm_num [h, sg, ZMod.val_one_eq_one_mod]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 2
  rw [hammingNorm, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

private lemma power_chars (m l : ℕ) (z : Fin m → ZMod 2) :
    (∑ a, sg (z a))^l =
      ∑ i : Fin l → Fin m, sg ((∑ j, basis (i j)) ⬝ᵥ z) := by
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_dotProduct, sg_sum]
  apply Finset.prod_congr rfl
  intro j _
  simp [basis, single_dotProduct]

private lemma fourier_chars (m l : ℕ) (S : Fin m → ZMod 2) :
    boolFourier (fun z => (∑ a, sg (z a))^l) S = (walkCount l S : ℝ) := by
  classical
  unfold boolFourier
  change ((2:ℝ)^m)⁻¹ * (∑ z, (∑ a, sg (z a))^l * sg (S ⬝ᵥ z)) = _
  simp_rw [power_chars, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  simp_rw [char_orth]
  simp only [walkCount, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

private lemma expansion {m T : ℕ} {β : ℝ} (hm : 0 < m) (S : Fin m → ZMod 2) :
    boolFourier (weightPowFun m β T) S =
      ∑ l ∈ Finset.range (T+1), (T.choose l : ℝ) * (1-β/2)^(T-l) *
        (β/(2*m))^l * (walkCount l S : ℝ) := by
  have hm' : (m:ℝ) ≠ 0 := by positivity
  have he (z : Fin m → ZMod 2) :
      weightPowFun m β T z =
        ∑ l ∈ Finset.range (T+1), (T.choose l : ℝ) * (1-β/2)^(T-l) *
          (β/(2*m))^l * (∑ a, sg (z a))^l := by
    unfold weightPowFun
    have hb : 1 - β*(hammingNorm z : ℝ)/(m:ℝ) =
        (β/(2*m))*(∑ a, sg (z a)) + (1-β/2) := by
      rw [sum_sg]; field_simp; ring
    rw [hb, add_pow]
    apply Finset.sum_congr rfl
    intro l _
    rw [mul_pow]; ring
  unfold boolFourier
  change ((2:ℝ)^m)⁻¹ * (∑ z, weightPowFun m β T z * sg (S ⬝ᵥ z)) = _
  simp_rw [he, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hf := fourier_chars m l S
  unfold boolFourier at hf
  change ((2:ℝ)^m)⁻¹ * (∑ z, (∑ a, sg (z a))^l * sg (S ⬝ᵥ z)) = _ at hf
  rw [← hf]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

private lemma toggle_weight {m : ℕ} (S : Fin m → ZMod 2) (a : Fin m) :
    (S a = 0 → hammingNorm (S + basis a) = hammingNorm S + 1) ∧
    (S a ≠ 0 → hammingNorm (S + basis a) + 1 = hammingNorm S) := by
  classical
  have scalar (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
    have hv : z.val = 1 := by
      have := ZMod.val_lt z
      have hn := (ZMod.val_eq_zero z).not.mpr hz
      omega
    exact ZMod.val_injective 2 (by simpa only [ZMod.val_one_eq_one_mod] using hv)
  constructor
  · intro h
    have he : (Finset.univ.filter fun b => (S + basis a) b ≠ 0) =
        insert a (Finset.univ.filter fun b => S b ≠ 0) := by
      ext b
      by_cases hb : b = a
      · subst b; simp [basis, h]
      · simp [basis, hb]
    change (Finset.univ.filter fun b => (S + basis a) b ≠ 0).card = _
    rw [he, Finset.card_insert_of_notMem (by simp [h])]; rfl
  · intro h
    have he : (Finset.univ.filter fun b => (S + basis a) b ≠ 0) =
        (Finset.univ.filter fun b => S b ≠ 0).erase a := by
      ext b
      by_cases hb : b = a
      · subst b; simp [basis, scalar _ h, CharTwo.add_self_eq_zero]
      · simp [basis, hb]
    rw [hammingNorm, he]
    exact Finset.card_erase_add_one (by simp [h])


private lemma walk_feasible {m l : ℕ} (i : Fin l → Fin m) :
    ∃ r : ℕ, l = hammingNorm (∑ j, basis (i j)) + 2*r := by
  induction l with
  | zero => exact ⟨0, by simp⟩
  | succ l ih =>
    let S := ∑ j : Fin l, basis (i j.succ)
    obtain ⟨r, hr⟩ := ih (fun j => i j.succ)
    change l = hammingNorm S + 2*r at hr
    rw [Fin.sum_univ_succ]
    change ∃ r, l+1 = hammingNorm (basis (i 0) + S) + 2*r
    rw [add_comm (basis (i 0)) S]
    by_cases h : S (i 0) = 0
    · exact ⟨r, by rw [(toggle_weight S (i 0)).1 h]; omega⟩
    · exact ⟨r+1, by have := (toggle_weight S (i 0)).2 h; omega⟩

private lemma walk_zero {m l : ℕ} (S : Fin m → ZMod 2)
    (h : ¬ ∃ r : ℕ, l = hammingNorm S + 2*r) : walkCount l S = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i _ hi
  exact h (hi ▸ walk_feasible i)

private lemma coefficient_bound {T l : ℕ} {a b c : ℝ}
    (hl : l ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : b ≤ a*c) :
    (T.choose l : ℝ) * a^(T-l) * b^l * (l.factorial : ℝ) ≤ a^T * ((T:ℝ)*c)^l := by
  have hp := pow_le_pow_left₀ hb hbc l
  have hf : (T.choose l : ℝ) * (l.factorial : ℝ) ≤ (T:ℝ)^l := by
    have h := Nat.descFactorial_le_pow T l
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    exact_mod_cast (by simpa [mul_comm] using h)
  calc
    _ ≤ (T.choose l : ℝ) * a^(T-l) * (a*c)^l * (l.factorial : ℝ) := by gcongr
    _ = a^T * ((T.choose l : ℝ) * (l.factorial : ℝ)) * c^l := by
      rw [mul_pow]
      have he : a^T = a^(T-l)*a^l := by rw [← pow_add, Nat.sub_add_cancel hl]
      rw [he]; ring
    _ ≤ a^T * (T:ℝ)^l * c^l := by gcongr
    _ = _ := by rw [mul_pow]; ring

private lemma term_bound {m T l r : ℕ} {a b c : ℝ} (S : Fin m → ZMod 2)
    (hl : l ≤ T) (hr : l = hammingNorm S + 2*r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : b ≤ a*c) :
    (T.choose l : ℝ) * a^(T-l) * b^l * (walkCount l S : ℝ) ≤
      a^T * ((T:ℝ)*c)^(hammingNorm S) *
        (((m:ℝ)*((T:ℝ)*c)^2/2)^r / (r.factorial : ℝ)) := by
  have he : Even (l-hammingNorm S) := ⟨r, by omega⟩
  have hd : (l-hammingNorm S)/2 = r := by omega
  have hn := (QAlgorithms.Arunachalam.count_basis_sums S (by omega : hammingNorm S ≤ l) hl).1 he
  rw [hd] at hn
  change (walkCount l S : ℝ) ≤ _ at hn
  have hcoef := coefficient_bound hl ha hb hc hbc
  have hden : (0:ℝ) < 2^r * (r.factorial : ℝ) := by positivity
  calc
    _ ≤ (T.choose l : ℝ) * a^(T-l) * b^l *
        ((l.factorial : ℝ)*(m:ℝ)^r/(2^r*(r.factorial : ℝ))) := by gcongr
    _ = ((T.choose l : ℝ) * a^(T-l) * b^l * (l.factorial : ℝ)) *
        ((m:ℝ)^r/(2^r*(r.factorial : ℝ))) := by ring
    _ ≤ (a^T * ((T:ℝ)*c)^l) * ((m:ℝ)^r/(2^r*(r.factorial : ℝ))) := by gcongr
    _ = _ := by rw [hr, pow_add, pow_mul, div_pow, mul_pow]; ring
-- The even-length excess is indexed by its number of pairs.
private lemma sum_bound {m T : ℕ} {a b c : ℝ} (S : Fin m → ZMod 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : b ≤ a*c) :
    (∑ l ∈ Finset.range (T+1), (T.choose l : ℝ) * a^(T-l) * b^l *
      (walkCount l S : ℝ)) ≤
      a^T * ((T:ℝ)*c)^(hammingNorm S) * Real.exp ((m:ℝ)*((T:ℝ)*c)^2/2) := by
  classical
  let q := hammingNorm S
  let F := (Finset.range (T+1)).filter (fun l => ∃ r : ℕ, l = q + 2*r)
  let g : ℕ → ℝ := fun r => ((m:ℝ)*((T:ℝ)*c)^2/2)^r / (r.factorial : ℝ)
  have hF (l : ℕ) (hl : l ∈ F) : l = q + 2*((l-q)/2) := by
    obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hl).2
    omega
  have hi : Set.InjOn (fun l => (l-q)/2) (↑F : Set ℕ) := by
    intro l hl k hk he
    change (l-q)/2 = (k-q)/2 at he
    have := hF l hl
    have := hF k hk
    omega
  have hs : F.image (fun l => (l-q)/2) ⊆ Finset.range (T+1) := by
    intro r hr
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hr
    have hlT := Finset.mem_range.mp (Finset.mem_filter.mp hl).1
    exact Finset.mem_range.mpr (by omega)
  calc
    _ = ∑ l ∈ F, (T.choose l : ℝ) * a^(T-l) * b^l * (walkCount l S : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro l hl hlf
      have hz : walkCount l S = 0 := by
        apply walk_zero
        intro he
        exact hlf (Finset.mem_filter.mpr ⟨hl, he⟩)
      rw [hz, Nat.cast_zero, mul_zero]
    _ ≤ ∑ l ∈ F, a^T * ((T:ℝ)*c)^q * g ((l-q)/2) := by
      apply Finset.sum_le_sum
      intro l hl
      exact term_bound S (by have := Finset.mem_range.mp (Finset.mem_filter.mp hl).1; omega)
        (hF l hl) ha hb hc hbc
    _ = a^T * ((T:ℝ)*c)^q * ∑ l ∈ F, g ((l-q)/2) := by rw [Finset.mul_sum]
    _ = a^T * ((T:ℝ)*c)^q * ∑ r ∈ F.image (fun l => (l-q)/2), g r := by
      rw [Finset.sum_image hi]
    _ ≤ a^T * ((T:ℝ)*c)^q * ∑ r ∈ Finset.range (T+1), g r := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; dsimp [g]; positivity))
        (by positivity)
    _ ≤ _ := by
      gcongr
      exact Real.sum_le_exp_of_nonneg (by positivity) (T+1)

theorem solution {m T : ℕ} {β : ℝ} (hm : 10 ≤ m) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (_hT : 1 ≤ T) (_hTm : (T : ℝ) ≤ (m : ℝ) / (Real.exp 3 * β)) (S : Fin m → ZMod 2) :
    0 ≤ boolFourier (weightPowFun m β T) S ∧
      boolFourier (weightPowFun m β T) S ≤
        4 * Real.exp 1 * (1 - β / 2) ^ T * ((T : ℝ) * β / (m : ℝ)) ^ hammingNorm S *
          Real.exp (22 * (T : ℝ) ^ 2 * β ^ 2 / (m : ℝ)) := by
  have hm0 : 0 < m := by omega
  have hm' : (0:ℝ) < m := by positivity
  have ha : 0 ≤ 1-β/2 := by linarith
  have hb : 0 ≤ β/(2*m) := by positivity
  have hc : 0 ≤ β/(m:ℝ) := by positivity
  have hbc : β/(2*m) ≤ (1-β/2)*(β/(m:ℝ)) := by
    field_simp
    nlinarith
  rw [expansion hm0]
  constructor
  · exact Finset.sum_nonneg (fun l _ => by positivity)
  · have h := sum_bound (T := T) S ha hb hc hbc
    have hx : (T:ℝ)*(β/(m:ℝ)) = (T:ℝ)*β/(m:ℝ) := by ring
    rw [hx] at h
    have he : (m:ℝ)*((T:ℝ)*β/(m:ℝ))^2/2 ≤ 22*(T:ℝ)^2*β^2/(m:ℝ) := by
      field_simp
      nlinarith [sq_nonneg ((T:ℝ)*β)]
    have hfour : (1:ℝ) ≤ 4*Real.exp 1 := by
      have := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)
      linarith
    calc
      _ ≤ (1-β/2)^T * ((T:ℝ)*β/(m:ℝ))^(hammingNorm S) *
          Real.exp ((m:ℝ)*((T:ℝ)*β/(m:ℝ))^2/2) := h
      _ ≤ (1-β/2)^T * ((T:ℝ)*β/(m:ℝ))^(hammingNorm S) *
          Real.exp (22*(T:ℝ)^2*β^2/(m:ℝ)) := by gcongr
      _ ≤ _ := by
        nlinarith [mul_nonneg
          (by positivity : 0 ≤ (1-β/2)^T * ((T:ℝ)*β/(m:ℝ))^(hammingNorm S) *
            Real.exp (22*(T:ℝ)^2*β^2/(m:ℝ))) (sub_nonneg.mpr hfour)]
