-- Prove2me | solution 1 for SignRankMargin.OREquality.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:53:52.418268+00:00
-- url     : https://prove2.me/submissions/56a4d860-b123-4c77-b514-20f2bbf67415

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_SignRankMargin_OREquality_Composition

section
namespace SignRankMargin.OREquality.Dev.L9

open Polynomial

/-- `H` has a factorization of width `R`. -/
def HasFact {X Y : Type*} (H : X → Y → ℝ) (R : ℕ) : Prop :=
  ∃ (f : X → Fin R → ℝ) (g : Y → Fin R → ℝ), ∀ x y, H x y = ∑ l, f x l * g y l

lemma HasFact.comp {X Y X' Y' : Type*} {H : X → Y → ℝ} {R : ℕ} (h : HasFact H R)
    (e : X' → X) (e' : Y' → Y) : HasFact (fun x y => H (e x) (e' y)) R := by
  obtain ⟨f, g, hfg⟩ := h
  exact ⟨fun x => f (e x), fun y => g (e' y), fun x y => hfg _ _⟩

lemma HasFact.smul {X Y : Type*} {H : X → Y → ℝ} {R : ℕ} (h : HasFact H R) (c : ℝ) :
    HasFact (fun x y => c * H x y) R := by
  obtain ⟨f, g, hfg⟩ := h
  refine ⟨fun x l => c * f x l, g, fun x y => ?_⟩
  dsimp only
  rw [hfg, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun l _ => by ring)

lemma HasFact.add {X Y : Type*} {H H' : X → Y → ℝ} {R S : ℕ} (h : HasFact H R)
    (h' : HasFact H' S) : HasFact (fun x y => H x y + H' x y) (R + S) := by
  obtain ⟨f, g, hfg⟩ := h
  obtain ⟨f', g', hfg'⟩ := h'
  refine ⟨fun x => Fin.append (f x) (f' x), fun y => Fin.append (g y) (g' y), fun x y => ?_⟩
  dsimp only
  rw [Fin.sum_univ_add, hfg, hfg']
  simp [Fin.append_left, Fin.append_right]

lemma HasFact.mul {X Y : Type*} {H H' : X → Y → ℝ} {R S : ℕ} (h : HasFact H R)
    (h' : HasFact H' S) : HasFact (fun x y => H x y * H' x y) (R * S) := by
  obtain ⟨f, g, hfg⟩ := h
  obtain ⟨f', g', hfg'⟩ := h'
  refine ⟨fun x p => f x (finProdFinEquiv.symm p).1 * f' x (finProdFinEquiv.symm p).2,
    fun y p => g y (finProdFinEquiv.symm p).1 * g' y (finProdFinEquiv.symm p).2, fun x y => ?_⟩
  dsimp only
  rw [hfg, hfg', Finset.sum_mul_sum]
  rw [(finProdFinEquiv.symm).sum_comp
    (fun q : Fin R × Fin S => (f x q.1 * f' x q.2) * (g y q.1 * g' y q.2)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma HasFact.cast {X Y : Type*} {H : X → Y → ℝ} {R S : ℕ} (h : HasFact H R) (hRS : R = S) :
    HasFact H S := hRS ▸ h

lemma hasFact_eval {X Y : Type*} (P : X → Polynomial ℝ) (n : ℕ)
    (hP : ∀ a, (P a).natDegree < n) (w z : Y → ℝ) :
    HasFact (fun a b => w b * (P a).eval (z b)) n := by
  refine ⟨fun a l => (P a).coeff l, fun b l => w b * z b ^ (l : ℕ), fun a b => ?_⟩
  dsimp only
  rw [Polynomial.eval_eq_sum_range' (hP a), Finset.sum_range, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun l _ => by ring)

lemma rank_le_of_hasFact {X Y : Type*} [Fintype X] [Fintype Y] {H : X → Y → ℝ} {R : ℕ}
    (h : HasFact H R) : (Matrix.of H).rank ≤ R := by
  classical
  obtain ⟨f, g, hfg⟩ := h
  have : Matrix.of H = (Matrix.of f : Matrix X (Fin R) ℝ) * (Matrix.of g : Matrix Y (Fin R) ℝ).transpose := by
    ext x y
    simp [Matrix.mul_apply, hfg]
  rw [this]
  calc _ ≤ (Matrix.of f : Matrix X (Fin R) ℝ).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin R) := Matrix.rank_le_card_width _
    _ = R := Fintype.card_fin R

lemma signRank_le_of_realizes {X Y : Type*} [Fintype X] [Fintype Y] (F : Matrix X Y Bool)
    (H : Matrix X Y ℝ) (hH : StrictRealizes F H) : signRank F ≤ H.rank := by
  classical
  unfold signRank
  exact Nat.find_min' _ ⟨H, hH, rfl⟩

lemma exists_lower {ι : Type*} [Fintype ι] (G : ι → ℝ) (hG : ∀ i, G i ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ |G i| := by
  refine ⟨1 / (1 + ∑ i, 1 / |G i|), by positivity, fun i => ?_⟩
  have hp : 0 < |G i| := abs_pos.2 (hG i)
  have h1 : 1 / |G i| ≤ ∑ i, 1 / |G i| :=
    Finset.single_le_sum (f := fun i => 1 / |G i|) (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 := one_div_le_one_div_of_le (by positivity : 0 < 1 / |G i|) (by linarith : 1 / |G i| ≤ 1 + ∑ i, 1 / |G i|)
  simpa using h2

lemma exists_scale {ι : Type*} [Fintype ι] (G : ι → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, |c * G i| ≤ 1 / 4 := by
  refine ⟨1 / (4 * (1 + ∑ i, |G i|)), by positivity, fun i => ?_⟩
  have h1 : |G i| ≤ ∑ i, |G i| :=
    Finset.single_le_sum (f := fun i => |G i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hS : 0 ≤ ∑ i, |G i| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (4 * (1 + ∑ i, |G i|)))]
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- One copy of `B`: the clearing-denominators matrices `E_T`, `F_T` of the paper. -/
lemma single_copy (D u v : ℕ) (hD : 1 ≤ D) (B : Matrix (Fin u) (Fin v) Bool)
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) ≤ D) (T : ℝ) (hT : 1 < T) :
    ∃ (E F : Fin u → Fin v → ℝ), HasFact E (D + 1) ∧ HasFact F D ∧ (∀ a b, 0 < E a b) ∧
      ∀ a b, ∃ R : ℝ, F a b = E a b * R ∧ 0 ≤ R ∧ (B a b = false → R ≤ D / T) ∧
        (B a b = true → 1 / 2 ≤ R) := by
  classical
  have hT0 : 0 < T := by linarith
  let S : Fin u → Finset (Fin v) := fun a => Finset.univ.filter (fun c => B a c = true)
  have hS : ∀ a, (S a).card ≤ D := by
    intro a
    exact le_trans (le_of_eq (Finset.card_filter (fun c => B a c = true) Finset.univ)) (hrows a)
  let P : Fin u → ℝ[X] := fun a => ∏ c ∈ S a, (X + C (T ^ (2 * c.val)))
  let Q : Fin u → ℝ[X] := fun a => ∑ c ∈ S a,
    C (T ^ c.val) * ∏ d ∈ (S a).erase c, (X + C (T ^ (2 * d.val)))
  have hPdeg : ∀ a, (P a).natDegree < D + 1 := by
    intro a
    have h1 : (P a).natDegree ≤ ∑ c ∈ S a, (X + C (T ^ (2 * c.val)) : ℝ[X]).natDegree :=
      Polynomial.natDegree_prod_le _ _
    simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one] at h1
    have := hS a
    omega
  have hQdeg : ∀ a, (Q a).natDegree < D := by
    intro a
    have h1 : (Q a).natDegree ≤ D - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro c hc
      refine le_trans (natDegree_C_mul_le _ _) ?_
      refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
      simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
      rw [Finset.card_erase_of_mem hc]
      have := hS a
      omega
    omega
  have hE := hasFact_eval P (D + 1) hPdeg (fun _ => (1:ℝ)) (fun b : Fin v => T ^ (2 * b.val))
  have hF := hasFact_eval Q D hQdeg (fun b : Fin v => T ^ b.val) (fun b : Fin v => T ^ (2 * b.val))
  refine ⟨fun a b => (P a).eval (T ^ (2 * b.val)),
    fun a b => T ^ b.val * (Q a).eval (T ^ (2 * b.val)), by simpa using hE, hF, ?_, ?_⟩
  · intro a b
    simp only [P, Polynomial.eval_prod, eval_add, eval_X, eval_C]
    exact Finset.prod_pos (fun c _ => by positivity)
  · intro a b
    refine ⟨∑ c ∈ S a, T ^ (b.val + c.val) / (T ^ (2 * b.val) + T ^ (2 * c.val)), ?_, ?_, ?_, ?_⟩
    · simp only [P, Q, Polynomial.eval_prod, eval_add, eval_X, eval_C, eval_finsetSum, eval_mul]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c hc => ?_)
      have hne : T ^ (2 * b.val) + T ^ (2 * c.val) ≠ 0 := by positivity
      rw [← Finset.mul_prod_erase (S a) (fun c => T ^ (2 * b.val) + T ^ (2 * c.val)) hc]
      rw [pow_add]
      field_simp
    · exact Finset.sum_nonneg (fun c _ => by positivity)
    · intro hBab
      have hterm : ∀ c ∈ S a, T ^ (b.val + c.val) / (T ^ (2 * b.val) + T ^ (2 * c.val)) ≤ 1 / T := by
        intro c hc
        have hBc : B a c = true := by simpa [S] using hc
        have hbc : b.val ≠ c.val := by
          intro h
          have : b = c := Fin.ext h
          rw [this] at hBab
          rw [hBab] at hBc
          exact Bool.false_ne_true hBc
        rw [div_le_div_iff₀ (by positivity) hT0, one_mul, ← pow_succ]
        rcases Nat.lt_or_gt_of_ne hbc with h | h
        · calc T ^ (b.val + c.val + 1) ≤ T ^ (2 * c.val) :=
              pow_le_pow_right₀ hT.le (by omega)
            _ ≤ _ := by have : 0 ≤ T ^ (2 * b.val) := by positivity
                        linarith
        · calc T ^ (b.val + c.val + 1) ≤ T ^ (2 * b.val) :=
              pow_le_pow_right₀ hT.le (by omega)
            _ ≤ _ := by have : 0 ≤ T ^ (2 * c.val) := by positivity
                        linarith
      calc _ ≤ ∑ c ∈ S a, 1 / T := Finset.sum_le_sum hterm
        _ = ((S a).card : ℝ) / T := by simp [div_eq_mul_inv]
        _ ≤ D / T := by
          gcongr
          exact_mod_cast hS a
    · intro hBab
      have hb : b ∈ S a := by simp [S, hBab]
      have h1 := Finset.single_le_sum
        (f := fun c => T ^ (b.val + c.val) / (T ^ (2 * b.val) + T ^ (2 * c.val)))
        (fun c _ => by positivity) hb
      refine le_trans (le_of_eq ?_) h1
      have : T ^ (2 * b.val) ≠ 0 := by positivity
      rw [← two_mul, ← two_mul]
      field_simp

/-- `H` has the sign pattern of the OR composition of `j` copies of `B`. -/
def Realizes {u v : ℕ} (B : Matrix (Fin u) (Fin v) Bool) (j : ℕ)
    (H : (Fin j → Fin u) → (Fin j → Fin v) → ℝ) : Prop :=
  (∀ x y, (∃ i, B (x i) (y i) = true) → 0 < H x y) ∧
    (∀ x y, ¬ (∃ i, B (x i) (y i) = true) → H x y < 0)

lemma step (D u v : ℕ) (hD : 1 ≤ D) (B : Matrix (Fin u) (Fin v) Bool)
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) ≤ D) (j W : ℕ)
    (H : (Fin j → Fin u) → (Fin j → Fin v) → ℝ) (hr : Realizes B j H) (hf : HasFact H W) :
    ∃ H' : (Fin (j + 1) → Fin u) → (Fin (j + 1) → Fin v) → ℝ,
      Realizes B (j + 1) H' ∧ HasFact H' ((D + 1) * W + D) := by
  classical
  have hne : ∀ x y, H x y ≠ 0 := by
    intro x y
    by_cases h : ∃ i, B (x i) (y i) = true
    · exact (hr.1 x y h).ne'
    · exact (hr.2 x y h).ne
  obtain ⟨c, hc, hcb⟩ := exists_scale (fun p : (Fin j → Fin u) × (Fin j → Fin v) => H p.1 p.2)
  obtain ⟨m, hm, hmb⟩ := exists_lower (fun p : (Fin j → Fin u) × (Fin j → Fin v) => c * H p.1 p.2)
    (fun p => mul_ne_zero hc.ne' (hne _ _))
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDm : 0 < (D : ℝ) / m := by positivity
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = (D : ℝ) / m + 1 := ⟨_, rfl⟩
  have hT : 1 < T := by rw [hTdef]; linarith
  have hDT : (D : ℝ) / T < m := by
    rw [div_lt_iff₀ (by linarith), hTdef]
    have : m * ((D : ℝ) / m + 1) = D + m := by field_simp
    rw [this]; linarith
  obtain ⟨E, F, hE, hFf, hEpos, hEF⟩ := single_copy D u v hD B hrows T hT
  refine ⟨fun x y => E (x 0) (y 0) * (c * H (Fin.tail x) (Fin.tail y)) + F (x 0) (y 0),
    ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    obtain ⟨R, hFR, hR0, hRf, hRt⟩ := hEF (x 0) (y 0)
    have hval : E (x 0) (y 0) * (c * H (Fin.tail x) (Fin.tail y)) + F (x 0) (y 0) =
        E (x 0) (y 0) * (c * H (Fin.tail x) (Fin.tail y) + R) := by rw [hFR]; ring
    dsimp only
    rw [hval]
    refine mul_pos (hEpos _ _) ?_
    have hor : B (x 0) (y 0) = true ∨ ∃ i : Fin j, B (Fin.tail x i) (Fin.tail y i) = true :=
      Fin.exists_fin_succ.1 hxy
    rcases hor with h | h
    · have h1 := hRt h
      have h2 := abs_le.1 (hcb (Fin.tail x, Fin.tail y))
      simp only at h2
      linarith [h2.1]
    · have := hr.1 _ _ h
      have := mul_pos hc this
      linarith
  · intro x y hxy
    obtain ⟨R, hFR, hR0, hRf, hRt⟩ := hEF (x 0) (y 0)
    have hval : E (x 0) (y 0) * (c * H (Fin.tail x) (Fin.tail y)) + F (x 0) (y 0) =
        E (x 0) (y 0) * (c * H (Fin.tail x) (Fin.tail y) + R) := by rw [hFR]; ring
    dsimp only
    rw [hval]
    have hnot : ¬ (B (x 0) (y 0) = true ∨ ∃ i : Fin j, B (Fin.tail x i) (Fin.tail y i) = true) :=
      fun h => hxy (Fin.exists_fin_succ.2 h)
    push Not at hnot
    have hb : B (x 0) (y 0) = false := by simpa using hnot.1
    have h1 := hRf hb
    have h3 : H (Fin.tail x) (Fin.tail y) < 0 := hr.2 _ _ (by simpa using hnot.2)
    have h4 : m ≤ |c * H (Fin.tail x) (Fin.tail y)| := hmb (Fin.tail x, Fin.tail y)
    have h5 : c * H (Fin.tail x) (Fin.tail y) < 0 := mul_neg_of_pos_of_neg hc h3
    rw [abs_of_neg h5] at h4
    exact mul_neg_of_pos_of_neg (hEpos _ _) (by linarith)
  · exact (((hE.comp (fun x : Fin (j + 1) → Fin u => x 0) (fun y : Fin (j + 1) → Fin v => y 0)).mul
      ((hf.smul c).comp (Fin.tail : (Fin (j + 1) → Fin u) → _) (Fin.tail : (Fin (j + 1) → Fin v) → _))).add
      (hFf.comp (fun x : Fin (j + 1) → Fin u => x 0) (fun y : Fin (j + 1) → Fin v => y 0)))

lemma width_succ (D j : ℕ) :
    (D + 1) * (2 * (D + 1) ^ j - 1) + D = 2 * (D + 1) ^ (j + 1) - 1 := by
  have h1 : 1 ≤ (D + 1) ^ j := Nat.one_le_pow _ _ (by omega)
  have h2 : (D + 1) ^ (j + 1) = (D + 1) * (D + 1) ^ j := by ring
  rw [h2]
  have : 1 ≤ 2 * (D + 1) ^ j := by omega
  zify [this, (by nlinarith : 1 ≤ 2 * ((D + 1) * (D + 1) ^ j))]
  ring

lemma main (D u v : ℕ) (hD : 1 ≤ D) (B : Matrix (Fin u) (Fin v) Bool)
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) ≤ D) (k : ℕ) :
    ∃ H : (Fin k → Fin u) → (Fin k → Fin v) → ℝ,
      Realizes B k H ∧ HasFact H (2 * (D + 1) ^ k - 1) := by
  induction k with
  | zero =>
    refine ⟨fun _ _ => -1, ⟨?_, ?_⟩, ?_⟩
    · rintro x y ⟨i, _⟩
      exact i.elim0
    · intro x y _
      norm_num
    · have : HasFact (fun (_ : Fin 0 → Fin u) (_ : Fin 0 → Fin v) => (-1 : ℝ)) 1 :=
        ⟨fun _ _ => 1, fun _ _ => -1, fun x y => by simp⟩
      exact this.cast (by simp)
  | succ j ih =>
    obtain ⟨H, hr, hf⟩ := ih
    obtain ⟨H', hr', hf'⟩ := step D u v hD B hrows j _ H hr hf
    exact ⟨H', hr', hf'.cast (width_succ D j)⟩

lemma bound (k D u v : ℕ) (hD : 1 ≤ D) (B : Matrix (Fin u) (Fin v) Bool)
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) ≤ D) :
    signRank (orComposition k B) ≤ 2 * (D + 1) ^ k - 1 := by
  obtain ⟨H, hr, hf⟩ := main D u v hD B hrows k
  have hstrict : StrictRealizes (orComposition k B) (Matrix.of H) := by
    intro x y
    by_cases h : ∃ i, B (x i) (y i) = true
    · have : orComposition k B x y = true := by simp [orComposition, h]
      simpa [this] using hr.1 x y h
    · have : orComposition k B x y = false := by simp [orComposition, h]
      simpa [this] using hr.2 x y h
  exact le_trans (signRank_le_of_realizes _ _ hstrict) (rank_le_of_hasFact hf)

end SignRankMargin.OREquality.Dev.L9

namespace SignRankMargin.OREquality

theorem chk_lemma_9 (k D u v : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (B : Matrix (Fin u) (Fin v) Bool)
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) ≤ D) :
    signRank (orComposition k B) ≤ 2 * (D + 1) ^ k - 1 ∧
    (∀ n : ℕ, 1 ≤ n → signRank (orEquality k n) ≤ 2 ^ (k + 1) - 1) := by
  refine ⟨Dev.L9.bound k D u v hD B hrows, fun n _ => ?_⟩
  have h := Dev.L9.bound k 1 (2 ^ n) (2 ^ n) le_rfl (equalityMatrix n) (fun x => by simp [equalityMatrix])
  have e : 2 * (1 + 1) ^ k = 2 ^ (k + 1) := by ring
  rw [e] at h
  exact h

end SignRankMargin.OREquality
end

theorem solution : type_of% @SignRankMargin.OREquality.chk_lemma_9 := @SignRankMargin.OREquality.chk_lemma_9
