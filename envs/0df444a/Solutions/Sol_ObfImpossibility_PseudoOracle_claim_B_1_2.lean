-- Prove2me | solution 1 for ObfImpossibility.PseudoOracle.claim_B_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-24T00:11:38.026228+00:00
-- url     : https://prove2.me/submissions/67d0ba20-48a4-4768-88ad-1930b1a12651

import Mathlib
import Theorems.Thm_ObfImpossibility_PseudoOracle_inequality_8

open ObfImpossibility.PseudoOracle Filter Classical
open scoped BigOperators

namespace WentaoCompression

-- Finite Chernoff and encoding helpers adapted from Nickrobbins95's accepted
-- lemma_B_1 proof (a95cccc5-e28b-46c6-a48b-7e4bc1bc3dea).
/-- Bool to real indicator. -/
noncomputable def b2r (b : Bool) : ℝ := if b then 1 else 0

lemma b2r_nonneg (b : Bool) : 0 ≤ b2r b := by cases b <;> simp [b2r]
lemma b2r_le_one (b : Bool) : b2r b ≤ 1 := by cases b <;> simp [b2r]
lemma b2r_not (b : Bool) : b2r (!b) = 1 - b2r b := by cases b <;> simp [b2r]

lemma avg_eq {α : Type} (s : Finset α) (f : α → Bool) :
    avg s f = (∑ a ∈ s, b2r (f a)) / s.card := by
  unfold avg
  congr 1
  rw [Finset.card_filter]
  push_cast
  rfl

lemma avg_nonneg {α : Type} (s : Finset α) (f : α → Bool) : 0 ≤ avg s f := by
  unfold avg; positivity

lemma avg_le_one {α : Type} (s : Finset α) (f : α → Bool) : avg s f ≤ 1 := by
  unfold avg
  rcases Nat.eq_zero_or_pos s.card with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_filter_le _ _

lemma exp_le_quad (x : ℝ) (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le hx
  have := (abs_le.mp this).2
  linarith

/-- Chernoff bound, counting form, for sampling with replacement from a finset `U`. -/
theorem chernoff_up {α : Type} [DecidableEq α] (U : Finset α) (hU : U.Nonempty) (f : α → Bool)
    (m : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        (avg U f + η) * m ≤ ∑ i, b2r (f (φ i))).card : ℝ) ≤
      Real.exp (-(m * η ^ 2 / 4)) * (U.card : ℝ) ^ m := by
  set P := Fintype.piFinset fun _ : Fin m => U with hP
  set lam := η / 2 with hlam
  set p := avg U f with hp
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hp0 : 0 ≤ p := avg_nonneg _ _
  have hp1 : p ≤ 1 := avg_le_one _ _
  have hlam0 : 0 < lam := by positivity
  have hW : ∑ u ∈ U, Real.exp (lam * b2r (f u)) = U.card * (1 + p * (Real.exp lam - 1)) := by
    have key : ∀ u, Real.exp (lam * b2r (f u)) = 1 + b2r (f u) * (Real.exp lam - 1) := by
      intro u; cases f u <;> simp [b2r]
    simp_rw [key, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hp, avg_eq]
    field_simp
    simp
  have hprod : ∑ φ ∈ P, Real.exp (lam * ∑ i, b2r (f (φ i))) =
      (∑ u ∈ U, Real.exp (lam * b2r (f u))) ^ m := by
    rw [← Fin.prod_const, Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro φ _
    rw [Finset.mul_sum, Real.exp_sum]
  have hmark : (((P.filter fun φ => (p + η) * m ≤ ∑ i, b2r (f (φ i))).card : ℝ)) *
      Real.exp (lam * ((p + η) * m)) ≤ ∑ φ ∈ P, Real.exp (lam * ∑ i, b2r (f (φ i))) := by
    calc _ = ∑ φ ∈ P.filter (fun φ => (p + η) * m ≤ ∑ i, b2r (f (φ i))),
          Real.exp (lam * ((p + η) * m)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ φ ∈ P.filter (fun φ => (p + η) * m ≤ ∑ i, b2r (f (φ i))),
          Real.exp (lam * ∑ i, b2r (f (φ i))) := by
          apply Finset.sum_le_sum
          intro φ hφ
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hφ).2 hlam0.le)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => (Real.exp_pos _).le)
  have h1 : 1 + p * (Real.exp lam - 1) ≤ Real.exp (p * (lam + lam ^ 2)) := by
    have hq := exp_le_quad lam (by rw [abs_le]; constructor <;> linarith)
    calc 1 + p * (Real.exp lam - 1) ≤ 1 + p * (lam + lam ^ 2) := by nlinarith
      _ ≤ _ := by linarith [Real.add_one_le_exp (p * (lam + lam ^ 2))]
  have hbase0 : 0 ≤ 1 + p * (Real.exp lam - 1) := by
    have : 1 ≤ Real.exp lam := Real.one_le_exp hlam0.le
    nlinarith
  have h2 : (1 + p * (Real.exp lam - 1)) ^ m ≤ Real.exp (m * (p * (lam + lam ^ 2))) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hbase0 h1 m
  have hE : 0 < Real.exp (lam * ((p + η) * m)) := Real.exp_pos _
  rw [hprod, hW, mul_pow] at hmark
  have h3 : (((P.filter fun φ => (p + η) * m ≤ ∑ i, b2r (f (φ i))).card : ℝ)) ≤
      (U.card : ℝ) ^ m * Real.exp (m * (p * (lam + lam ^ 2))) / Real.exp (lam * ((p + η) * m)) := by
    rw [le_div_iff₀ hE]
    calc _ ≤ (U.card : ℝ) ^ m * (1 + p * (Real.exp lam - 1)) ^ m := hmark
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  refine h3.trans ?_
  rw [mul_div_assoc, ← Real.exp_sub, mul_comm (Real.exp _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [hlam]
  nlinarith [mul_nonneg hm (mul_nonneg (sub_nonneg.mpr hp1) (sq_nonneg (η / 2)))]


/-- Lower tail, from the upper tail applied to the negated function. -/
theorem chernoff_down {α : Type} [DecidableEq α] (U : Finset α) (hU : U.Nonempty) (f : α → Bool)
    (m : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        ∑ i, b2r (f (φ i)) ≤ (avg U f - η) * m).card : ℝ) ≤
      Real.exp (-(m * η ^ 2 / 4)) * (U.card : ℝ) ^ m := by
  have h := chernoff_up U hU (fun a => !f a) m η hη0 hη1
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have havg : avg U (fun a => !f a) = 1 - avg U f := by
    rw [avg_eq, avg_eq]
    simp_rw [b2r_not, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    field_simp
  refine le_trans (le_of_eq ?_) h
  congr 2
  ext φ
  simp only [Finset.mem_filter, havg, b2r_not, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> nlinarith

/-- Two-sided Chernoff. -/
theorem chernoff_two {α : Type} [DecidableEq α] (U : Finset α) (hU : U.Nonempty) (f : α → Bool)
    (m : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        η * m ≤ |∑ i, b2r (f (φ i)) - avg U f * m|).card : ℝ) ≤
      2 * Real.exp (-(m * η ^ 2 / 4)) * (U.card : ℝ) ^ m := by
  have h1 := chernoff_up U hU f m η hη0 hη1
  have h2 := chernoff_down U hU f m η hη0 hη1
  have hsub : ((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        η * m ≤ |∑ i, b2r (f (φ i)) - avg U f * m|) ⊆
      ((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        (avg U f + η) * m ≤ ∑ i, b2r (f (φ i))) ∪
      ((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        ∑ i, b2r (f (φ i)) ≤ (avg U f - η) * m) := by
    intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_union] at hφ ⊢
    rcases le_abs'.mp hφ.2 with h | h
    · right; exact ⟨hφ.1, by nlinarith⟩
    · left; exact ⟨hφ.1, by nlinarith⟩
  calc _ ≤ ((((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        (avg U f + η) * m ≤ ∑ i, b2r (f (φ i))) ∪
      ((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        ∑ i, b2r (f (φ i)) ≤ (avg U f - η) * m)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := by
        refine le_trans (Nat.cast_le.mpr (Finset.card_union_le _ _)) ?_
        push_cast
        linarith


/-- `n^m ≤ 2 n^{(m)}` when `4 m^2 ≤ n`. -/
lemma pow_le_two_descFactorial (n m : ℕ) (h : 4 * m ^ 2 ≤ n) :
    (n : ℝ) ^ m ≤ 2 * (n.descFactorial m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  have hn : 0 < n := by nlinarith
  have hmn : m ≤ n := by nlinarith
  have h1 : ((n + 1 - m : ℕ) : ℝ) ^ m ≤ n.descFactorial m := by
    exact_mod_cast Nat.pow_sub_le_descFactorial n m
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : ((n : ℝ) - m) ≤ ((n + 1 - m : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have h3 : (0 : ℝ) ≤ n - m := by
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hb := one_add_mul_le_pow (a := -((m : ℝ) / n)) (by
    have : (m : ℝ) / n ≤ 1 := by rw [div_le_one hnr]; exact_mod_cast hmn
    have : 0 ≤ (m : ℝ) / n := by positivity
    linarith) m
  have hmm : (4 : ℝ) * (m : ℝ) ^ 2 ≤ n := by exact_mod_cast h
  have h4 : (1 : ℝ) / 2 ≤ 1 + (m : ℝ) * -((m : ℝ) / n) := by
    rw [mul_neg, ← mul_div_assoc, ← sq]
    have : (m : ℝ) ^ 2 / n ≤ 1 / 4 := by
      rw [div_le_iff₀ hnr]; linarith
    linarith
  have h5 : (1 + -((m : ℝ) / n)) ^ m * (n : ℝ) ^ m = ((n : ℝ) - m) ^ m := by
    rw [← mul_pow]; congr 1; field_simp; ring
  have h6 : ((n : ℝ) - m) ^ m ≤ ((n + 1 - m : ℕ) : ℝ) ^ m := pow_le_pow_left₀ h3 h2 m
  have h7 : (1 / 2 : ℝ) * (n : ℝ) ^ m ≤ ((n : ℝ) - m) ^ m := by
    rw [← h5]
    exact mul_le_mul_of_nonneg_right (h4.trans hb) (by positivity)
  linarith


private lemma runAvoid_congr {K L : ℕ} (t : QTree K L)
    (G G' : Fin K → Fin L) (S : Finset (Fin K))
    (hG : ∀ z, z ∉ S → G' z = G z) :
    t.runAvoid G' S = t.runAvoid G S := by
  induction t with
  | out b => rfl
  | query z k ih =>
    by_cases hz : z ∈ S
    · simp [QTree.runAvoid, hz]
    · simpa only [QTree.runAvoid, if_neg hz, hG z hz] using ih (G z)


section Sim
variable {K L : ℕ}

def sim (D : Fin L → QTree K L) (S : Finset (Fin K)) (g : Fin K → Fin L) (y : Fin L) : Bool :=
  (D y).runAvoid g S

def LGf (S : Finset (Fin K)) (g : Fin K → Fin L) : Finset (Fin L) :=
  Finset.univ \ ((Finset.univ.filter fun x => x ∉ S).image g)

lemma sim_congr (D : Fin L → QTree K L) (S : Finset (Fin K)) (g g' : Fin K → Fin L)
    (h : ∀ z, z ∉ S → g z = g' z) : sim D S g = sim D S g' := by
  funext y
  exact runAvoid_congr (D y) g' g S h

lemma LGf_congr (S : Finset (Fin K)) (g g' : Fin K → Fin L)
    (h : ∀ z, z ∉ S → g z = g' z) : LGf S g = LGf S g' := by
  unfold LGf
  congr 1
  apply Finset.image_congr
  intro z hz
  exact h z (Finset.mem_filter.mp hz).2


lemma card_LGf (S : Finset (Fin K)) (g : Fin K → Fin L)
    (hg : Set.InjOn g ↑(Finset.univ.filter fun x => x ∉ S)) :
    (LGf S g).card = L - (K - S.card) := by
  unfold LGf
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_image_of_injOn hg]
  congr 1
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- The encoding count for one sample embedding `s`. -/
lemma encode_count (D : Fin L → QTree K L) {m : ℕ} (s : Fin m ↪ Fin K) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η ≤ 1) (hKL : K < L) :
    ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
        η * m ≤ |∑ i, b2r (sim D (Finset.univ.image s) G (G (s i))) -
          avg (LGf (Finset.univ.image s) G) (sim D (Finset.univ.image s) G) * m|).card : ℝ) ≤
      2 * Real.exp (-(m * η ^ 2 / 4)) * ((L - K + m : ℕ) : ℝ) ^ m *
        (L.descFactorial (K - m) : ℝ) := by
  classical
  set S : Finset (Fin K) := Finset.univ.image s with hS
  have hScard : S.card = m := by
    rw [hS, Finset.card_image_of_injective _ s.injective]; simp
  have hmK : m ≤ K := by
    have := Finset.card_le_univ S
    rw [hScard, Fintype.card_fin] at this; exact this
  let T := {x : Fin K // x ∉ S}
  have y0 : Fin L := ⟨0, by omega⟩
  let ext : (T ↪ Fin L) → Fin K → Fin L := fun H x => if h : x ∈ S then y0 else H ⟨x, h⟩
  let r : (Fin K ↪ Fin L) → (T ↪ Fin L) := fun G => (Function.Embedding.subtype _).trans G
  have hext : ∀ G : Fin K ↪ Fin L, ∀ z, z ∉ S → ext (r G) z = G z := by
    intro G z hz
    simp only [ext, r, hz, dif_neg, not_false_eq_true, Function.Embedding.trans_apply]
    rfl
  let cond : (T ↪ Fin L) → (Fin m → Fin L) → Prop := fun H φ =>
    η * m ≤ |∑ i, b2r (sim D S (ext H) (φ i)) - avg (LGf S (ext H)) (sim D S (ext H)) * m|
  let tgt : Finset (Σ _ : (T ↪ Fin L), (Fin m → Fin L)) :=
    (Finset.univ : Finset (T ↪ Fin L)).sigma
      (fun H => (Fintype.piFinset fun _ : Fin m => LGf S (ext H)).filter (cond H))
  let Φ : (Fin K ↪ Fin L) → (Σ _ : (T ↪ Fin L), (Fin m → Fin L)) :=
    fun G => ⟨r G, fun i => G (s i)⟩
  have hcardLG : ∀ H : T ↪ Fin L, (LGf S (ext H)).card = L - K + m := by
    intro H
    rw [card_LGf, hScard]
    · omega
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      simp only [ext, ha, hb, dif_neg, not_false_eq_true] at hab
      exact congrArg Subtype.val (H.injective hab)
  have hmaps : Set.MapsTo Φ ↑(Finset.univ.filter fun G : Fin K ↪ Fin L =>
        η * m ≤ |∑ i, b2r (sim D S G (G (s i))) - avg (LGf S G) (sim D S G) * m|) ↑tgt := by
    intro G hG
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hG
    simp only [tgt, Φ, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ,
      true_and, Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset]
    have hsim : sim D S (ext (r G)) = sim D S G := sim_congr D S _ _ (hext G)
    have hLG : LGf S (ext (r G)) = LGf S G := LGf_congr S _ _ (hext G)
    refine ⟨?_, ?_⟩
    · intro i
      rw [hLG]
      unfold LGf
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_filter, not_exists, not_and]
      intro x hx hxe
      apply hx
      have := G.injective hxe
      rw [this, hS]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · show cond (r G) (fun i => G (s i))
      simp only [cond, hsim, hLG]
      exact hG
  have hinj : Set.InjOn Φ ↑(Finset.univ.filter fun G : Fin K ↪ Fin L =>
        η * m ≤ |∑ i, b2r (sim D S G (G (s i))) - avg (LGf S G) (sim D S G) * m|) := by
    intro G1 _ G2 _ h
    simp only [Φ, Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    have h2' := eq_of_heq h2
    ext x
    by_cases hx : x ∈ S
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hS ▸ hx)
      exact congrArg Fin.val (congrFun h2' i)
    · have := congrArg (fun H : T ↪ Fin L => H ⟨x, hx⟩) h1
      simp only [r, Function.Embedding.trans_apply, Function.Embedding.subtype_apply] at this
      exact congrArg Fin.val this
  have hle := Finset.card_le_card_of_injOn Φ hmaps hinj
  have hT : Fintype.card T = K - m := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    simp [hScard]
  have hU : ∀ H : T ↪ Fin L, (LGf S (ext H)).Nonempty := by
    intro H
    rw [← Finset.card_pos, hcardLG]
    omega
  calc _ ≤ (tgt.card : ℝ) := by exact_mod_cast hle
    _ = ∑ H : T ↪ Fin L, (((Fintype.piFinset fun _ : Fin m => LGf S (ext H)).filter
          (cond H)).card : ℝ) := by
        simp only [tgt, Finset.card_sigma]; push_cast; rfl
    _ ≤ ∑ _H : T ↪ Fin L, 2 * Real.exp (-(m * η ^ 2 / 4)) * ((L - K + m : ℕ) : ℝ) ^ m := by
        apply Finset.sum_le_sum
        intro H _
        have := chernoff_two (LGf S (ext H)) (hU H) (sim D S (ext H)) m η hη0 hη1
        rw [hcardLG H] at this
        exact this
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, hT, Fintype.card_fin,
          nsmul_eq_mul]
        ring

end Sim

def flipTree {K L : ℕ} : QTree K L → QTree K L
  | .out b => .out (!b)
  | .query z k => .query z (fun y => flipTree (k y))

lemma flip_run {K L : ℕ} (t : QTree K L) (G : Fin K → Fin L) :
    (flipTree t).run G = !(t.run G) := by
  induction t with
  | out b => rfl
  | query z k ih => exact ih (G z)

lemma flip_hits {K L : ℕ} (t : QTree K L) (G : Fin K → Fin L) (S : Finset (Fin K)) :
    (flipTree t).hits G S = t.hits G S := by
  induction t with
  | out b => rfl
  | query z k ih => simp only [flipTree, QTree.hits, ih]

lemma avg_not {α : Type} (S : Finset α) (hS : 0 < S.card) (f : α → Bool) :
    avg S (fun x => !f x) = 1 - avg S f := by
  rw [avg_eq, avg_eq]
  simp_rw [b2r_not, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  field_simp

lemma LGf_eq {K L : ℕ} (S : Finset (Fin K)) (G : Fin K ↪ Fin L) : LGf S G = LG G S := by
  simp [LGf, LG, Finset.filter_not, Finset.map_eq_image]

lemma avg_sample {K m : ℕ} (s : Fin m ↪ Fin K) (f : Fin K → Bool) :
    avg (Finset.univ.image s) f = (∑ i, b2r (f (s i))) / m := by
  rw [avg_eq, Finset.card_image_of_injective _ s.injective]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_image]
  exact fun a _ b _ h => s.injective h

lemma fixed_subset {K L : ℕ} (hKL : K < L) (D : Fin L → QTree K L) (δ : ℝ)
    (SG : Finset (Fin K)) (hm : 0 < SG.card)
    (hcollision : 4 * SG.card ^ 2 ≤ L - K + SG.card)
    (hη : 0 < 1 / (2 * (K : ℝ) ^ δ)) (hη1 : 1 / (2 * (K : ℝ) ^ δ) ≤ 1) :
    ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
        (∀ x ∈ SG, (D (G x)).hits G SG = false) ∧
        1 / (2 * (K : ℝ) ^ δ) <
          |avg SG (fun x => (D (G x)).run G) - avg (LG G SG) (fun y => (D y).run G)|).card : ℝ) ≤
      8 * Real.exp (-(SG.card * (1 / (2 * (K : ℝ) ^ δ)) ^ 2 / 4)) *
        (Fintype.card (Fin K ↪ Fin L) : ℝ) := by
  classical
  let m := SG.card
  let s : Fin m ↪ Fin K := (SG.orderEmbOfFin rfl).toEmbedding
  have hs : Finset.univ.image s = SG := Finset.image_orderEmbOfFin_univ SG rfl
  let η := 1 / (2 * (K : ℝ) ^ δ)
  let D' : Fin L → QTree K L := fun y => flipTree (D y)
  let E (D₀ : Fin L → QTree K L) := Finset.univ.filter fun G : Fin K ↪ Fin L =>
    η * m ≤ |∑ i, b2r (sim D₀ (Finset.univ.image s) G (G (s i))) -
      avg (LGf (Finset.univ.image s) G) (sim D₀ (Finset.univ.image s) G) * m|
  have hsub : (Finset.univ.filter fun G : Fin K ↪ Fin L =>
        (∀ x ∈ SG, (D (G x)).hits G SG = false) ∧
        η < |avg SG (fun x => (D (G x)).run G) - avg (LG G SG) (fun y => (D y).run G)|) ⊆
      E D ∪ E D' := by
    intro G hG
    obtain ⟨_, hno, hgap⟩ := Finset.mem_filter.mp hG
    have hLG : 0 < (LG G SG).card := by
      rw [← LGf_eq, card_LGf]
      · omega
      · exact fun a _ b _ h => G.injective h
    have encode (D₀ : Fin L → QTree K L)
        (hno₀ : ∀ x ∈ SG, (D₀ (G x)).hits G SG = false)
        (hgap₀ : η < avg SG (fun x => (D₀ (G x)).run G) -
          avg (LG G SG) (fun y => (D₀ y).run G)) : G ∈ E D₀ := by
      have hi := (inequality_8 K L δ D₀ G SG hno₀ hgap₀).2
      have hisample : avg SG (fun x => (D₀ (G x)).runAvoid G SG) =
          (∑ i, b2r (sim D₀ SG G (G (s i)))) / m := by
        rw [← hs]
        exact avg_sample s (fun x => sim D₀ (Finset.univ.image s) G (G x))
      have hmr : (0 : ℝ) < m := by exact_mod_cast hm
      rw [hisample] at hi
      have hscaled : η * m < ∑ i, b2r (sim D₀ SG G (G (s i))) -
          avg (LG G SG) (sim D₀ SG G) * m := by
        change η < (∑ i, b2r (sim D₀ SG G (G (s i)))) / m -
          avg (LG G SG) (sim D₀ SG G) at hi
        have hh : η + avg (LG G SG) (sim D₀ SG G) <
            (∑ i, b2r (sim D₀ SG G (G (s i)))) / m := by linarith
        have hh' := (lt_div_iff₀ hmr).mp hh
        nlinarith
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hs, LGf_eq]
      exact hscaled.le.trans (le_abs_self _)
    rcases lt_abs.mp hgap with hpos | hneg
    · exact Finset.mem_union_left _ (encode D hno hpos)
    · apply Finset.mem_union_right
      apply encode D'
      · intro x hx
        simpa only [D', flip_hits] using hno x hx
      · have ha : avg SG (fun x => (D' (G x)).run G) =
            1 - avg SG (fun x => (D (G x)).run G) := by
          simp only [D', flip_run]
          exact avg_not SG hm _
        have hb : avg (LG G SG) (fun y => (D' y).run G) =
            1 - avg (LG G SG) (fun y => (D y).run G) := by
          simp only [D', flip_run]
          exact avg_not _ hLG _
        rw [ha, hb]
        linarith
  have he1 := encode_count D s η hη hη1 hKL
  have he2 := encode_count D' s η hη hη1 hKL
  have hcard : ((E D ∪ E D').card : ℝ) ≤
      4 * Real.exp (-(m * η ^ 2 / 4)) * ((L - K + m : ℕ) : ℝ) ^ m *
        (L.descFactorial (K - m) : ℝ) := by
    have hh : ((E D ∪ E D').card : ℝ) ≤ (E D).card + (E D').card := by
      exact_mod_cast Finset.card_union_le (E D) (E D')
    dsimp only [E] at hh
    linarith
  have hpow := pow_le_two_descFactorial (L - K + m) m hcollision
  have hmK : m ≤ K := by dsimp [m]; simpa using Finset.card_le_univ SG
  have hfactor : (L - K + m).descFactorial m * L.descFactorial (K - m) = L.descFactorial K := by
    have hh := Nat.descFactorial_mul_descFactorial (n := L) (m := K) (k := K - m) (by omega)
    simpa only [show K - (K - m) = m by omega,
      show L - (K - m) = L - K + m by omega] using hh
  have hbound : 4 * Real.exp (-(m * η ^ 2 / 4)) * ((L - K + m : ℕ) : ℝ) ^ m *
        (L.descFactorial (K - m) : ℝ) ≤
      8 * Real.exp (-(m * η ^ 2 / 4)) * (L.descFactorial K : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4 * Real.exp (-(m * η ^ 2 / 4))))
      (Nat.cast_nonneg (L.descFactorial (K - m)) : (0 : ℝ) ≤ _)
    have hf : ((L - K + m).descFactorial m : ℝ) * (L.descFactorial (K - m) : ℝ) =
        (L.descFactorial K : ℝ) := by exact_mod_cast hfactor
    calc
      _ ≤ 4 * Real.exp (-(m * η ^ 2 / 4)) *
          (2 * ((L - K + m).descFactorial m : ℝ)) *
          (L.descFactorial (K - m) : ℝ) := hh
      _ = _ := by rw [show 4 * Real.exp (-(m * η ^ 2 / 4)) *
          (2 * ((L - K + m).descFactorial m : ℝ)) * (L.descFactorial (K - m) : ℝ) =
          8 * Real.exp (-(m * η ^ 2 / 4)) *
          (((L - K + m).descFactorial m : ℝ) * (L.descFactorial (K - m) : ℝ)) by ring, hf]
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  exact (show _ ≤ ((E D ∪ E D').card : ℝ) by exact_mod_cast Finset.card_le_card hsub).trans
    (hcard.trans hbound)

lemma near_count {α : Type} [DecidableEq α] (S : Finset α) (γ lam : ℝ) (hlam : 0 ≤ lam) :
    ((S.powerset.filter fun T => (1 - γ) * S.card ≤ (T.card : ℝ)).card : ℝ) ≤
      Real.exp ((S.card : ℝ) * Real.exp (-lam) + lam * γ * S.card) := by
  classical
  let A := S.powerset.filter fun T => (1 - γ) * S.card ≤ (T.card : ℝ)
  have hexpand : (∑ T ∈ S.powerset, Real.exp (-lam * ((S.card : ℝ) - T.card))) =
      (1 + Real.exp (-lam)) ^ S.card := by
    calc
      _ = ∑ R ∈ S.powerset, (Real.exp (-lam)) ^ R.card := by
        apply Finset.sum_bij (fun T _ => S \ T)
        · intro T _
          exact Finset.mem_powerset.mpr Finset.sdiff_subset
        · intro T hT U hU h
          have hh := congrArg (fun R => S \ R) h
          simpa only [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hT),
            Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hU)] using hh
        · intro R hR
          exact ⟨S \ R, Finset.mem_powerset.mpr Finset.sdiff_subset,
            Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hR)⟩
        · intro T hT
          rw [← Real.exp_nat_mul, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hT),
            Nat.cast_sub (Finset.card_le_card (Finset.mem_powerset.mp hT))]
          congr 1 <;> ring
      _ = _ := by
        simpa only [Finset.prod_const] using
          (Finset.prod_one_add (f := fun _ : α => Real.exp (-lam)) S).symm
  have hmark : (A.card : ℝ) * Real.exp (-lam * γ * S.card) ≤
      ∑ T ∈ S.powerset, Real.exp (-lam * ((S.card : ℝ) - T.card)) := by
    calc
      _ = ∑ _T ∈ A, Real.exp (-lam * γ * S.card) := by simp
      _ ≤ ∑ T ∈ A, Real.exp (-lam * ((S.card : ℝ) - T.card)) := by
        apply Finset.sum_le_sum
        intro T hT
        have hcard := (Finset.mem_filter.mp hT).2
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => (Real.exp_pos _).le)
  have hpow : (1 + Real.exp (-lam)) ^ S.card ≤
      Real.exp ((S.card : ℝ) * Real.exp (-lam)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (Real.exp (-lam))]) _
  rw [hexpand] at hmark
  have hle := hmark.trans hpow
  change (A.card : ℝ) ≤ _
  calc
    _ ≤ Real.exp ((S.card : ℝ) * Real.exp (-lam)) / Real.exp (-lam * γ * S.card) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr hle
    _ = _ := by rw [← Real.exp_sub]; congr 1 <;> ring

end WentaoCompression

open WentaoCompression in
set_option maxHeartbeats 2000000 in
theorem solution :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ,
      ∀ K L : ℕ, K₀ ≤ K → K ^ 2 ≤ L →
        ∀ D : Fin L → QTree K L, (∀ y, ((D y).depth : ℝ) ≤ (K : ℝ) ^ δ) →
          ∀ S : Finset (Fin K), S.card = ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊ →
            ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
                ∃ SG : Finset (Fin K), GoodSubset D δ S G SG).card : ℝ) ≤
              (Fintype.card (Fin K ↪ Fin L) : ℝ) *
                (2 : ℝ) ^ (-(c * (K : ℝ) ^ (1 - 7 * δ))) := by
  classical
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro δ hδ hδ1
  have hα : 0 < 1 - 5 * δ := by linarith
  have hβ : 0 < 1 - 7 * δ := by linarith
  have tq := (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  have tl : Tendsto (fun K : ℕ => Real.log (K : ℝ) / (K : ℝ) ^ δ) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have ti : Tendsto (fun K : ℕ => (1 : ℝ) / (K : ℝ) ^ δ) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tq
  have tlog : Tendsto (fun K : ℕ => (1 + 3 * δ * Real.log (K : ℝ)) / (K : ℝ) ^ δ)
      atTop (nhds 0) := by
    have hf : (fun K : ℕ => (1 + 3 * δ * Real.log (K : ℝ)) / (K : ℝ) ^ δ) =
        (fun K : ℕ => 1 / (K : ℝ) ^ δ + (3 * δ) * (Real.log (K : ℝ) / (K : ℝ) ^ δ)) := by
      funext K
      ring
    rw [hf]
    simpa only [mul_zero, add_zero] using ti.add (tl.const_mul (3 * δ))
  have elog : ∀ᶠ K : ℕ in atTop,
      (1 + 3 * δ * Real.log (K : ℝ)) / (K : ℝ) ^ δ < 1 / 256 :=
    (tendsto_order.mp tlog).2 _ (by norm_num)
  have eA := ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 : ℝ)
  have eH := ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1792 : ℝ)
  have eγ := ((tendsto_rpow_atTop (by linarith : 0 < 3 * δ)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 : ℝ)
  have e10 := ((tendsto_rpow_atTop (by linarith : 0 < 10 * δ)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (8 : ℝ)
  have ev : ∀ᶠ K : ℕ in atTop,
      2 ≤ K ∧ 2 ≤ (K : ℝ) ^ (1 - 5 * δ) ∧ 1792 ≤ (K : ℝ) ^ (1 - 7 * δ) ∧
      2 ≤ (K : ℝ) ^ (3 * δ) ∧ 8 ≤ (K : ℝ) ^ (10 * δ) ∧
      (1 + 3 * δ * Real.log (K : ℝ)) / (K : ℝ) ^ δ < 1 / 256 := by
    filter_upwards [eventually_ge_atTop 2, eA, eH, eγ, e10, elog] with K h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp ev
  refine ⟨1 / 128, by norm_num, N, ?_⟩
  intro K L hKN hKL D _hD S hS
  obtain ⟨hK2, hA2, hHlarge, hKγ, hK10, hlog⟩ := hN K hKN
  have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hKr1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hKL' : K < L := by nlinarith
  have hKLr : (K : ℝ) ^ 2 ≤ L := by exact_mod_cast hKL
  let A := (K : ℝ) ^ (1 - 5 * δ)
  let H := (K : ℝ) ^ (1 - 7 * δ)
  let q := (K : ℝ) ^ δ
  let γ := (K : ℝ) ^ (-(3 * δ))
  let lam := 3 * δ * Real.log (K : ℝ)
  let B : ℝ := Fintype.card (Fin K ↪ Fin L)
  let F := S.powerset.filter fun T => (1 - γ) * S.card ≤ (T.card : ℝ)
  let E (T : Finset (Fin K)) := Finset.univ.filter fun G : Fin K ↪ Fin L =>
    (∀ x ∈ T, (D (G x)).hits G T = false) ∧
    1 / (2 * (K : ℝ) ^ δ) <
      |avg T (fun x => (D (G x)).run G) - avg (LG G T) (fun y => (D y).run G)|
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 ≤ q := by dsimp [q]; exact Real.one_le_rpow hKr1 hδ.le
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγhalf : γ ≤ 1 / 2 := by
    dsimp [γ]
    rw [Real.rpow_neg hKr.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hKγ
  have hlam : 0 ≤ lam := by dsimp [lam]; exact mul_nonneg (by positivity) (Real.log_nonneg hKr1)
  have hH : 0 < H := by dsimp [H]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hSupper : (S.card : ℝ) ≤ A := by rw [hS]; exact Nat.floor_le (by positivity)
  have hSlower : A / 2 ≤ (S.card : ℝ) := by
    rw [hS]
    have hh := Nat.lt_floor_add_one A
    dsimp [A] at *
    linarith
  have hHdiv : H = A / q ^ 2 := by
    dsimp [H, A, q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hKr.le, ← Real.rpow_sub hKr]
    congr 1 <;> ring
  have hγq : A * γ * q = H := by
    dsimp [A, γ, q, H]
    rw [← Real.rpow_add hKr, ← Real.rpow_add hKr]
    congr 1 <;> ring
  have hAsq : A ^ 2 * (K : ℝ) ^ (10 * δ) = (K : ℝ) ^ 2 := by
    dsimp [A]
    conv_lhs => rw [← Real.rpow_natCast, ← Real.rpow_mul hKr.le, ← Real.rpow_add hKr]
    have he : (1 - 5 * δ) * ((2 : ℕ) : ℝ) + 10 * δ = (2 : ℝ) := by push_cast; ring
    rw [he, Real.rpow_two]
  have hη : 0 < 1 / (2 * (K : ℝ) ^ δ) := by positivity
  have hη1 : 1 / (2 * (K : ℝ) ^ δ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    change 1 ≤ 2 * q
    linarith
  have hfixed (T : Finset (Fin K)) (hT : T ∈ F) :
      ((E T).card : ℝ) ≤ 8 * Real.exp (-(H / 64)) * B := by
    obtain ⟨hTS, hTcard⟩ := Finset.mem_filter.mp hT
    have hTS' : T ⊆ S := Finset.mem_powerset.mp hTS
    have hTupper : (T.card : ℝ) ≤ A :=
      (show (T.card : ℝ) ≤ S.card by exact_mod_cast Finset.card_le_card hTS').trans hSupper
    have hTlower : A / 4 ≤ (T.card : ℝ) := by nlinarith
    have hTm : 0 < T.card := by
      have : (0 : ℝ) < T.card := by dsimp [A] at hTlower; linarith
      exact_mod_cast this
    have hcollision : 4 * T.card ^ 2 ≤ L - K + T.card := by
      have hAsq8 : 8 * A ^ 2 ≤ (K : ℝ) ^ 2 := by
        rw [← hAsq]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hK10 (sq_nonneg A)
      have hTsq : (T.card : ℝ) ^ 2 ≤ A ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hTupper 2
      have hcolr : (4 : ℝ) * (T.card : ℝ) ^ 2 ≤ ((L - K + T.card : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_sub hKL'.le]
        have hKr2 : (2 : ℝ) ≤ K := by exact_mod_cast hK2
        nlinarith
      exact_mod_cast hcolr
    have hcount := fixed_subset hKL' D δ T hTm hcollision hη hη1
    have hrate : H / 64 ≤ (T.card : ℝ) * (1 / (2 * (K : ℝ) ^ δ)) ^ 2 / 4 := by
      have heq : H / 64 = (A / 4) * (1 / (2 * (K : ℝ) ^ δ)) ^ 2 / 4 := by
        rw [hHdiv]
        change _ = (A / 4) * (1 / (2 * q)) ^ 2 / 4
        field_simp
        <;> ring
      rw [heq]
      gcongr
    exact hcount.trans (by
      dsimp only [B]
      gcongr)
  have hFcount : (F.card : ℝ) ≤ Real.exp (H / 256) := by
    have hh := near_count S γ lam hlam
    have hexp : Real.exp (-lam) = γ := by
      dsimp [lam, γ]
      rw [Real.rpow_def_of_pos hKr]
      congr 1 <;> ring
    rw [hexp] at hh
    refine hh.trans (Real.exp_le_exp.mpr ?_)
    have hl : 1 + lam ≤ q / 256 := by
      have hh := (div_lt_iff₀ hq).mp hlog
      change 1 + lam < (1 / 256 : ℝ) * q at hh
      linarith
    have hmul := mul_le_mul hSupper hl (by positivity : 0 ≤ 1 + lam) (by dsimp [A]; positivity)
    have hmul' := mul_le_mul_of_nonneg_left hmul hγ.le
    nlinarith [hγq]
  have hsub : (Finset.univ.filter fun G : Fin K ↪ Fin L => ∃ T, GoodSubset D δ S G T) ⊆
      F.biUnion E := by
    intro G hG
    obtain ⟨_, T, hTS, hTcard, hno, hgap⟩ := Finset.mem_filter.mp hG
    apply Finset.mem_biUnion.mpr
    exact ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTS, hTcard⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hno, hgap⟩⟩
  have htotal : ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
      ∃ T, GoodSubset D δ S G T).card : ℝ) ≤
        Real.exp (H / 256) * (8 * Real.exp (-(H / 64)) * B) := by
    calc
      _ ≤ ((F.biUnion E).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ T ∈ F, ((E T).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _T ∈ F, 8 * Real.exp (-(H / 64)) * B :=
        Finset.sum_le_sum (fun T hT => hfixed T hT)
      _ = (F.card : ℝ) * (8 * Real.exp (-(H / 64)) * B) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hFcount (by positivity)
  have h8 : 8 * Real.exp (H / 256 - H / 64) ≤ Real.exp (-(H / 128)) := by
    have hlarge : 8 ≤ Real.exp (H / 256) := by
      linarith [Real.add_one_le_exp (H / 256)]
    have heq : Real.exp (H / 256 - H / 64) =
        Real.exp (-(H / 128)) / Real.exp (H / 256) := by
      rw [← Real.exp_sub]
      congr 1 <;> ring
    rw [heq, mul_div_assoc', div_le_iff₀ (Real.exp_pos _)]
    nlinarith [mul_le_mul_of_nonneg_left hlarge (Real.exp_pos (-(H / 128))).le]
  have hbase : Real.exp (-(H / 128)) ≤ (2 : ℝ) ^ (-(H / 128)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.log_two_lt_d9]
  calc
    _ ≤ Real.exp (H / 256) * (8 * Real.exp (-(H / 64)) * B) := htotal
    _ = (8 * Real.exp (H / 256 - H / 64)) * B := by rw [Real.exp_sub, Real.exp_neg]; ring
    _ ≤ Real.exp (-(H / 128)) * B := mul_le_mul_of_nonneg_right h8 hB
    _ ≤ (2 : ℝ) ^ (-(H / 128)) * B := mul_le_mul_of_nonneg_right hbase hB
    _ = B * (2 : ℝ) ^ (-((1 / 128 : ℝ) * H)) := by
      rw [mul_comm]
      congr 2 <;> ring

