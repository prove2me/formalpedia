-- Prove2me | solution 1 for ResolvingNRM.FRUpper.lemma8_bound_on_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:24:43.862264+00:00
-- url     : https://prove2.me/submissions/b9d9b014-ec4b-4679-baba-83f0e968d829

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_FRUpper_Model

open RLPBidPrice.Unbiased Matrix

namespace FRGapAux

lemma sum_cons {α : Type*} [Fintype α] (N : ℕ) (F : (Fin (N+1) → α) → ℝ) :
    ∑ ω, F ω = ∑ a, ∑ ω' : Fin N → α, F (Fin.cons a ω') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ (fun _ => rfl)).symm

lemma moments {α : Type*} [Fintype α] (u s : α → ℝ) : ∀ N : ℕ,
    (∑ ω : Fin N → α, ∏ i, u (ω i)) = (∑ a, u a) ^ N ∧
    (∑ ω : Fin N → α, (∏ i, u (ω i)) * ∑ i, s (ω i)) =
      N * (∑ a, u a * s a) * (∑ a, u a) ^ (N - 1) ∧
    (∑ ω : Fin N → α, (∏ i, u (ω i)) * (∑ i, s (ω i)) ^ 2) =
      N * (∑ a, u a * s a ^ 2) * (∑ a, u a) ^ (N - 1) +
        N * (N - 1 : ℝ) * (∑ a, u a * s a) ^ 2 * (∑ a, u a) ^ (N - 2) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have e0 : (∑ ω : Fin (N+1) → α, ∏ i, u (ω i)) =
        (∑ a, u a) * ∑ ω : Fin N → α, ∏ i, u (ω i) := by
      rw [sum_cons, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ω _ => ?_
      rw [Fin.prod_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]
    have e1 : (∑ ω : Fin (N+1) → α, (∏ i, u (ω i)) * ∑ i, s (ω i)) =
        (∑ a, u a * s a) * (∑ ω : Fin N → α, ∏ i, u (ω i)) +
          (∑ a, u a) * ∑ ω : Fin N → α, (∏ i, u (ω i)) * ∑ i, s (ω i) := by
      rw [sum_cons, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; ring
    have e2 : (∑ ω : Fin (N+1) → α, (∏ i, u (ω i)) * (∑ i, s (ω i)) ^ 2) =
        (∑ a, u a * s a ^ 2) * (∑ ω : Fin N → α, ∏ i, u (ω i)) +
        (∑ a, 2 * (u a * s a)) * (∑ ω : Fin N → α, (∏ i, u (ω i)) * ∑ i, s (ω i)) +
        (∑ a, u a) * ∑ ω : Fin N → α, (∏ i, u (ω i)) * (∑ i, s (ω i)) ^ 2 := by
      rw [sum_cons, Finset.sum_mul_sum, Finset.sum_mul_sum,
        Finset.sum_mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; ring
    refine ⟨?_, ?_, ?_⟩
    · rw [e0, h0, pow_succ]; ring
    · rw [e1, h0, h1]
      rcases N with _ | N
      · simp
      · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        rw [pow_succ]; ring
    · rw [e2, h0, h1, h2, ← Finset.mul_sum]
      rcases N with _ | N
      · simp
      · rcases N with _ | N
        · simp; ring
        · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
          rw [show N + 1 + 1 - 2 = N from rfl, show N + 1 + 1 + 1 - 2 = N + 1 from rfl,
            pow_succ _ N, pow_succ _ (N+1)]
          ring


/-- Functions bounded on the nonnegative orthant. -/
def BddNN {m : ℕ} (g : (Fin m → ℝ) → ℝ) : Prop := ∃ B, ∀ c, 0 ≤ c → |g c| ≤ B

/-- The properties of an expectation functional (on functions of the nonnegative state). -/
structure IsExp {m : ℕ} (E : ((Fin m → ℝ) → ℝ) → ℝ) : Prop where
  bound : ∀ g B, (∀ c, 0 ≤ c → |g c| ≤ B) → |E g| ≤ B
  lin : ∀ g h, BddNN g → BddNN h → ∀ a b : ℝ,
    E (fun c => a * g c + b * h c) = a * E g + b * E h
  mono : ∀ g h, BddNN g → BddNN h → (∀ c, 0 ≤ c → g c ≤ h c) → E g ≤ E h
  const : ∀ a : ℝ, E (fun _ => a) = a

lemma bddNN_const {m : ℕ} (a : ℝ) : BddNN (m := m) (fun _ => a) := ⟨|a|, fun _ _ => le_refl _⟩

lemma bddNN_lin {m : ℕ} {g h : (Fin m → ℝ) → ℝ} (hg : BddNN g) (hh : BddNN h) (a b : ℝ) :
    BddNN (fun c => a * g c + b * h c) := by
  obtain ⟨B, hB⟩ := hg
  obtain ⟨B', hB'⟩ := hh
  refine ⟨|a| * B + |b| * B', fun c hc => ?_⟩
  calc |a * g c + b * h c| ≤ |a * g c| + |b * h c| := abs_add_le _ _
    _ = |a| * |g c| + |b| * |h c| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * B + |b| * B' := by
        gcongr
        · exact hB c hc
        · exact hB' c hc

lemma IsExp.congr {m : ℕ} {E : ((Fin m → ℝ) → ℝ) → ℝ} (hE : IsExp E) {g h : (Fin m → ℝ) → ℝ}
    (hg : BddNN g) (hh : BddNN h) (he : ∀ c, 0 ≤ c → g c = h c) : E g = E h :=
  le_antisymm (hE.mono g h hg hh fun c hc => (he c hc).le)
    (hE.mono h g hh hg fun c hc => (he c hc).ge)

lemma IsExp.sum {m : ℕ} {ι : Type*} {E : ((Fin m → ℝ) → ℝ) → ℝ} (hE : IsExp E)
    (s : Finset ι) (a : ι → ℝ) (f : ι → (Fin m → ℝ) → ℝ) (hf : ∀ i, BddNN (f i)) :
    BddNN (fun c => ∑ i ∈ s, a i * f i c) ∧ E (fun c => ∑ i ∈ s, a i * f i c) = ∑ i ∈ s, a i * E (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨bddNN_const 0, hE.const 0⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    obtain ⟨hb, he⟩ := ih
    have key := hE.lin (f i) (fun c => ∑ i ∈ s, a i * f i c) (hf i) hb (a i) 1
    simp only [one_mul] at key
    refine ⟨?_, ?_⟩
    · have := bddNN_lin (hf i) hb (a i) 1
      simpa only [one_mul] using this
    · rw [key, he]

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)

lemma runWindow_nonneg : ∀ (L : List (Fin n × Bool)) (c : Fin m → ℝ), 0 ≤ c →
    0 ≤ (ResolvingNRM.IRT.runWindow A r L c).2
  | [], c, hc => by simpa [ResolvingNRM.IRT.runWindow] using hc
  | (j, b) :: rest, c, hc => by
      simp only [ResolvingNRM.IRT.runWindow]
      split_ifs with h
      · exact runWindow_nonneg rest _ (fun l => by have := h.2 l; simp only [Pi.zero_apply]; linarith)
      · exact runWindow_nonneg rest c hc

lemma poisson_hasSum (μ : ℝ) : HasSum (fun N => ResolvingNRM.IRT.poissonPMF μ N) 1 := by
  have h := ProbabilityTheory.hasSum_one_poissonMeasure (μ.toNNReal)
  have e : ((μ.toNNReal : NNReal) : ℝ) = max μ 0 := Real.coe_toNNReal' μ
  rw [e] at h
  simpa [ResolvingNRM.IRT.poissonPMF] using h

lemma poisson_nonneg (μ : ℝ) (N : ℕ) : 0 ≤ ResolvingNRM.IRT.poissonPMF μ N := by
  unfold ResolvingNRM.IRT.poissonPMF
  have : 0 ≤ max μ 0 := le_max_right _ _
  positivity

lemma mass_eq (p : Fin n → ℝ) (N : ℕ) :
    ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
      (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i)))
      = (∑ j, lam j / ∑ j, lam j) ^ N := by
  rw [Fintype.sum_pow]
  refine Finset.sum_congr rfl fun cls _ => ?_
  rw [← Fintype.prod_sum (fun i (β : Bool) =>
      (lam (cls i) / ∑ j, lam j) * (if β then p (cls i) else 1 - p (cls i)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  ring

lemma poisson_mass (hlam : ∀ j, 0 < lam j) (N : ℕ) :
    ResolvingNRM.IRT.poissonPMF ((∑ j, lam j) * 1) N * (∑ j, lam j / ∑ j, lam j) ^ N
      = ResolvingNRM.IRT.poissonPMF ((∑ j, lam j) * 1) N := by
  rw [← Finset.sum_div]
  by_cases h : (∑ j, lam j) = 0
  · rw [h]
    rcases N with _ | N
    · simp
    · simp [ResolvingNRM.IRT.poissonPMF]
  · rw [div_self h]; simp

/-- The one-window expectation functional is an expectation. -/
lemma window_isExp (hlam : ∀ j, 0 < lam j) (p : Fin n → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (c : Fin m → ℝ) (hc : 0 ≤ c) :
    IsExp (fun G => ResolvingNRM.FRUpper.windowExp A r lam 1 p c (fun _ c' => G c')) := by
  set Λ := ∑ j, lam j with hΛ
  set π : ℕ → ℝ := fun N => ResolvingNRM.IRT.poissonPMF (Λ * 1) N with hπ
  set w : (N : ℕ) → (Fin N → Fin n) → (Fin N → Bool) → ℝ := fun N cls coin =>
    ∏ i, (lam (cls i) / Λ) * (if coin i then p (cls i) else 1 - p (cls i)) with hw
  set o : (N : ℕ) → (Fin N → Fin n) → (Fin N → Bool) → (Fin m → ℝ) := fun N cls coin =>
    (ResolvingNRM.IRT.runWindow A r (List.ofFn fun i => (cls i, coin i)) c).2 with ho
  set I : ((Fin m → ℝ) → ℝ) → ℕ → ℝ := fun G N =>
    ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, w N cls coin * G (o N cls coin) with hI
  have hE : ∀ G, ResolvingNRM.FRUpper.windowExp A r lam 1 p c (fun _ c' => G c')
      = ∑' N, π N * I G N := fun G => rfl
  have hπs : HasSum π 1 := poisson_hasSum _
  have hπ0 : ∀ N, 0 ≤ π N := fun N => poisson_nonneg _ _
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun j _ => (hlam j).le
  have hw0 : ∀ N cls coin, 0 ≤ w N cls coin := by
    intro N cls coin
    apply Finset.prod_nonneg
    intro i _
    apply mul_nonneg (div_nonneg (hlam _).le hΛ0)
    split_ifs
    · exact hp0 _
    · have := hp1 (cls i); simp only [Pi.one_apply] at this; linarith
  have ho0 : ∀ N cls coin, 0 ≤ o N cls coin := fun N cls coin =>
    runWindow_nonneg A r _ c hc
  have hmass : ∀ N, π N * (∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, w N cls coin) = π N := by
    intro N
    have := mass_eq lam p N
    simp only [hw, hΛ] at this ⊢
    rw [this]
    exact poisson_mass lam hlam N
  -- linearity of I
  have hIlin : ∀ G H a b N, I (fun c => a * G c + b * H c) N = a * I G N + b * I H N := by
    intro G H a b N
    simp only [hI, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hIconst : ∀ a N, π N * I (fun _ => a) N = a * π N := by
    intro a N
    have : I (fun _ => a) N = a * ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, w N cls coin := by
      simp only [hI, Finset.mul_sum]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [this, mul_left_comm, hmass]
  have hIbound : ∀ G B, (∀ c, 0 ≤ c → |G c| ≤ B) → ∀ N, |π N * I G N| ≤ B * π N := by
    intro G B hG N
    have h1 : |I G N| ≤ B * ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, w N cls coin := by
      simp only [hI, Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun cls _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun coin _ => ?_)
      rw [abs_mul, abs_of_nonneg (hw0 N cls coin), mul_comm B]
      exact mul_le_mul_of_nonneg_left (hG _ (ho0 N cls coin)) (hw0 N cls coin)
    rw [abs_mul, abs_of_nonneg (hπ0 N)]
    calc π N * |I G N| ≤ π N * (B * ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, w N cls coin) :=
          mul_le_mul_of_nonneg_left h1 (hπ0 N)
      _ = B * (π N * ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, w N cls coin) := by ring
      _ = B * π N := by rw [hmass]
  have hsum : ∀ G, BddNN G → Summable fun N => π N * I G N := by
    rintro G ⟨B, hB⟩
    exact Summable.of_norm_bounded (hπs.summable.mul_left B) fun N => by
      rw [Real.norm_eq_abs]; exact hIbound G B hB N
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G B hG
    rw [hE]
    have hs : Summable fun N => π N * I G N := hsum G ⟨B, hG⟩
    have hb : Summable fun N => B * π N := hπs.summable.mul_left B
    have htot : ∑' N, B * π N = B := by rw [hπs.summable.tsum_mul_left, hπs.tsum_eq, mul_one]
    rw [abs_le]
    constructor
    · have := Summable.tsum_le_tsum (f := fun N => -(B * π N)) (g := fun N => π N * I G N)
        (fun N => by have := hIbound G B hG N; rw [abs_le] at this; linarith) hb.neg hs
      rw [tsum_neg, htot] at this; exact this
    · have := Summable.tsum_le_tsum (g := fun N => B * π N) (f := fun N => π N * I G N)
        (fun N => by have := hIbound G B hG N; rw [abs_le] at this; linarith) hs hb
      rw [htot] at this; exact this
  · intro G H hG hH a b
    simp only [hE]
    have e : ∀ N, π N * I (fun c => a * G c + b * H c) N = a * (π N * I G N) + b * (π N * I H N) := by
      intro N; rw [hIlin]; ring
    simp only [e]
    rw [Summable.tsum_add ((hsum G hG).mul_left a) ((hsum H hH).mul_left b),
      (hsum G hG).tsum_mul_left, (hsum H hH).tsum_mul_left]
  · intro G H hG hH hle
    simp only [hE]
    refine Summable.tsum_le_tsum (fun N => ?_) (hsum G hG) (hsum H hH)
    apply mul_le_mul_of_nonneg_left _ (hπ0 N)
    simp only [hI]
    exact Finset.sum_le_sum fun cls _ => Finset.sum_le_sum fun coin _ =>
      mul_le_mul_of_nonneg_left (hle _ (ho0 N cls coin)) (hw0 N cls coin)
  · intro a
    simp only [hE]
    simp only [hIconst]
    rw [hπs.summable.tsum_mul_left, hπs.tsum_eq, mul_one]


lemma sel_probs (hlam : ∀ j, 0 < lam j) (sel : (Fin m → ℝ) → (Fin n → ℝ))
    (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel) (b : Fin m → ℝ) (hb : 0 ≤ b) :
    0 ≤ ResolvingNRM.FRUpper.frProbs lam (sel b) ∧ ResolvingNRM.FRUpper.frProbs lam (sel b) ≤ 1 := by
  obtain ⟨⟨-, h0, h1⟩, -⟩ := hsel b hb
  constructor
  · intro j; exact div_nonneg (h0 j) (hlam j).le
  · intro j; exact div_le_one_of_le₀ (h1 j) (hlam j).le

/-- Expectations along FR are expectation functionals. -/
lemma frState_isExp (hlam : ∀ j, 0 < lam j) (sel : (Fin m → ℝ) → (Fin n → ℝ))
    (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel) :
    ∀ t k (c : Fin m → ℝ), 0 ≤ c →
      IsExp (fun g => ResolvingNRM.FRUpper.frStateExp A r lam sel k t g c) := by
  intro t
  induction t with
  | zero =>
    intro k c hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g B hg; simp only [ResolvingNRM.FRUpper.frStateExp]; exact hg c hc
    · intro g h _ _ a b; simp only [ResolvingNRM.FRUpper.frStateExp]
    · intro g h _ _ hle; simp only [ResolvingNRM.FRUpper.frStateExp]; exact hle c hc
    · intro a; simp only [ResolvingNRM.FRUpper.frStateExp]
  | succ t ih =>
    intro k c hc
    have hb : 0 ≤ (fun l => c l / (k : ℝ)) := fun l => div_nonneg (hc l) (Nat.cast_nonneg k)
    obtain ⟨hp0, hp1⟩ := sel_probs A r lam hlam sel hsel _ hb
    have W := window_isExp A r lam hlam _ hp0 hp1 c hc
    have e : ∀ g, ResolvingNRM.FRUpper.frStateExp A r lam sel k (t + 1) g c =
        ResolvingNRM.FRUpper.windowExp A r lam 1
          (ResolvingNRM.FRUpper.frProbs lam (sel fun l => c l / (k : ℝ))) c
          (fun _ c' => ResolvingNRM.FRUpper.frStateExp A r lam sel (k - 1) t g c') := fun g => rfl
    have hbdd : ∀ g, BddNN g →
        BddNN (fun c' => ResolvingNRM.FRUpper.frStateExp A r lam sel (k - 1) t g c') := by
      rintro g ⟨B, hB⟩
      exact ⟨B, fun c' hc' => (ih (k - 1) c' hc').bound g B hB⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g B hg
      rw [e]
      exact W.bound _ B fun c' hc' => (ih (k - 1) c' hc').bound g B hg
    · intro g h hg hh a b
      simp only [e]
      rw [W.congr (hbdd _ (bddNN_lin hg hh a b)) (bddNN_lin (hbdd g hg) (hbdd h hh) a b)
        (fun c' hc' => (ih (k - 1) c' hc').lin g h hg hh a b)]
      exact W.lin _ _ (hbdd g hg) (hbdd h hh) a b
    · intro g h hg hh hle
      simp only [e]
      exact W.mono _ _ (hbdd g hg) (hbdd h hh)
        (fun c' hc' => (ih (k - 1) c' hc').mono g h hg hh hle)
    · intro a
      simp only [e]
      rw [W.congr (hbdd _ (bddNN_const a)) (bddNN_const a)
        (fun c' hc' => (ih (k - 1) c' hc').const a)]
      exact W.const a


lemma poisson_succ (μ : ℝ) (hμ : 0 ≤ μ) (N : ℕ) :
    ResolvingNRM.IRT.poissonPMF μ (N + 1) * ((N : ℝ) + 1) = μ * ResolvingNRM.IRT.poissonPMF μ N := by
  unfold ResolvingNRM.IRT.poissonPMF
  rw [max_eq_left hμ, Nat.factorial_succ]
  push_cast
  have : (N.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma poisson_mom1 (μ : ℝ) (hμ : 0 ≤ μ) :
    HasSum (fun N => ResolvingNRM.IRT.poissonPMF μ N * N) μ := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  have : (fun N : ℕ => ResolvingNRM.IRT.poissonPMF μ (N + 1) * ((N : ℝ) + 1)) =
      fun N => μ * ResolvingNRM.IRT.poissonPMF μ N := funext (poisson_succ μ hμ)
  rw [this]
  simpa using (poisson_hasSum μ).mul_left μ

lemma poisson_mom2 (μ : ℝ) (hμ : 0 ≤ μ) :
    HasSum (fun N => ResolvingNRM.IRT.poissonPMF μ N * ((N : ℝ) * ((N : ℝ) - 1))) (μ ^ 2) := by
  apply (hasSum_nat_add_iff' 2).mp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    zero_mul, mul_zero, sub_self, zero_add, sub_zero, Nat.cast_add, Nat.cast_ofNat]
  have : (fun N : ℕ => ResolvingNRM.IRT.poissonPMF μ (N + 2) * (((N : ℝ) + 2) * ((N : ℝ) + 2 - 1))) =
      fun N => μ ^ 2 * ResolvingNRM.IRT.poissonPMF μ N := by
    funext N
    have h1 := poisson_succ μ hμ (N + 1)
    have h2 := poisson_succ μ hμ N
    push_cast at h1
    have e : ((N : ℝ) + 2) * ((N : ℝ) + 2 - 1) = ((N : ℝ) + 1 + 1) * ((N : ℝ) + 1) := by ring
    rw [e, ← mul_assoc, h1, mul_assoc, h2]; ring
  rw [this]
  simpa using (poisson_hasSum μ).mul_left (μ ^ 2)

variable {A} in
lemma runWindow_lower (hA : ∀ l j, 0 ≤ A l j) (l : Fin m) :
    ∀ (L : List (Fin n × Bool)) (c : Fin m → ℝ),
      c l - (L.map (fun x => if x.2 then A l x.1 else 0)).sum ≤ (ResolvingNRM.IRT.runWindow A r L c).2 l
  | [], c => by simp [ResolvingNRM.IRT.runWindow]
  | (j, b) :: rest, c => by
      have h0 : 0 ≤ (if b = true then A l j else 0) := by split_ifs <;> simp [hA l j]
      simp only [ResolvingNRM.IRT.runWindow, List.map_cons, List.sum_cons]
      by_cases h : b = true ∧ ∀ l, A l j ≤ c l
      · rw [if_pos h]
        have := runWindow_lower hA l rest (fun l => c l - A l j)
        simp only [h.1, if_true] at this ⊢
        linarith
      · rw [if_neg h]
        have := runWindow_lower hA l rest c
        linarith

lemma sum_cls_coin (N : ℕ) (H : (Fin N → Fin n) → (Fin N → Bool) → ℝ) :
    ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, H cls coin =
      ∑ ω : Fin N → Fin n × Bool, H (fun i => (ω i).1) (fun i => (ω i).2) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Fin n) (fun _ => Bool)).symm
    _ _ (fun _ => rfl))

lemma quad_bound (β0 m y : ℝ) :
    (max (β0 - y) 0) ^ 2 ≤ (max (β0 - m) 0) ^ 2 - 2 * max (β0 - m) 0 * (y - m) + (y - m) ^ 2 := by
  rcases le_total (β0 - y) 0 with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg (max (β0 - m) 0 - (y - m))]
  · rw [max_eq_left h]
    have hg : β0 - m ≤ max (β0 - m) 0 := le_max_left _ _
    have : β0 - y ≤ max (β0 - m) 0 - (y - m) := by linarith
    nlinarith

/-- One FR window: the quadratic shortfall grows by at most the variance term. -/
lemma window_quad (hlam : ∀ j, 0 < lam j) (hA : ∀ l j, 0 ≤ A l j) (x : Fin n → ℝ) (hx0 : 0 ≤ x)
    (hx1 : x ≤ lam) (c : Fin m → ℝ) (hc : 0 ≤ c) (κ : ℝ) (hκ : 0 < κ) (β0 : ℝ) (hβ : 0 ≤ β0)
    (l : Fin m) :
    ResolvingNRM.FRUpper.windowExp A r lam 1 (ResolvingNRM.FRUpper.frProbs lam x) c
        (fun _ c' => (max (β0 - c' l / κ) 0) ^ 2)
      ≤ (max (β0 - (c l - ∑ j, A l j * x j) / κ) 0) ^ 2 + (∑ j, A l j ^ 2 * x j) / κ ^ 2 := by
  set p := ResolvingNRM.FRUpper.frProbs lam x with hp
  set Λ := ∑ j, lam j with hΛ
  set μ := ∑ j, A l j * x j with hμ
  set σ2 := ∑ j, A l j ^ 2 * x j with hσ2
  set G := max (β0 - (c l - μ) / κ) 0 with hG
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun j _ => (hlam j).le
  have hp0 : 0 ≤ p := fun j => div_nonneg (hx0 j) (hlam j).le
  have hp1 : p ≤ 1 := fun j => div_le_one_of_le₀ (hx1 j) (hlam j).le
  set π : ℕ → ℝ := fun N => ResolvingNRM.IRT.poissonPMF (Λ * 1) N with hπ
  set u : Fin n × Bool → ℝ := fun a => (lam a.1 / Λ) * (if a.2 then p a.1 else 1 - p a.1) with hu
  set sf : Fin n × Bool → ℝ := fun a => if a.2 then A l a.1 else 0 with hsf
  set F : (Fin m → ℝ) → ℝ := fun c' => (max (β0 - c' l / κ) 0) ^ 2 with hF
  set o : (N : ℕ) → (Fin N → Fin n × Bool) → (Fin m → ℝ) := fun N ω =>
    (ResolvingNRM.IRT.runWindow A r (List.ofFn fun i => ((ω i).1, (ω i).2)) c).2 with ho
  set P : ℝ → ℝ := fun S => G ^ 2 - 2 * G * ((c l - S) / κ - (c l - μ) / κ) +
    ((c l - S) / κ - (c l - μ) / κ) ^ 2 with hP
  have hu0 : ∀ a, 0 ≤ u a := by
    intro a
    apply mul_nonneg (div_nonneg (hlam _).le hΛ0)
    split_ifs
    · exact hp0 _
    · have := hp1 a.1; simp only [Pi.one_apply] at this; linarith
  -- the window as a tsum over ω
  have hE : ResolvingNRM.FRUpper.windowExp A r lam 1 p c (fun _ c' => F c') =
      ∑' N, π N * ∑ ω : Fin N → Fin n × Bool, (∏ i, u (ω i)) * F (o N ω) := by
    unfold ResolvingNRM.FRUpper.windowExp
    refine tsum_congr fun N => ?_
    congr 1
    rw [sum_cls_coin]
  -- pointwise bound
  have hpt : ∀ N (ω : Fin N → Fin n × Bool), F (o N ω) ≤ P (∑ i, sf (ω i)) := by
    intro N ω
    have hlow := runWindow_lower r hA l (List.ofFn fun i => ((ω i).1, (ω i).2)) c
    rw [List.map_ofFn, List.sum_ofFn] at hlow
    simp only [Function.comp_def] at hlow
    have hmono : max (β0 - (o N ω) l / κ) 0 ≤ max (β0 - (c l - ∑ i, sf (ω i)) / κ) 0 := by
      apply max_le_max _ (le_refl _)
      have : (c l - ∑ i, sf (ω i)) / κ ≤ (o N ω) l / κ := div_le_div_of_nonneg_right hlow hκ.le
      linarith
    have h0 : 0 ≤ max (β0 - (o N ω) l / κ) 0 := le_max_right _ _
    calc F (o N ω) = (max (β0 - (o N ω) l / κ) 0) ^ 2 := rfl
      _ ≤ (max (β0 - (c l - ∑ i, sf (ω i)) / κ) 0) ^ 2 := pow_le_pow_left₀ h0 hmono 2
      _ ≤ _ := quad_bound β0 ((c l - μ) / κ) ((c l - ∑ i, sf (ω i)) / κ)
  have hF0 : ∀ c', 0 ≤ F c' := fun c' => sq_nonneg _
  -- moments
  have hM := fun N => moments u sf N
  set q := ∑ a, u a with hq
  set M1 := ∑ a, u a * sf a with hM1
  set M2 := ∑ a, u a * sf a ^ 2 with hM2
  -- expansion of the polynomial
  have hPexp : ∀ S, P S = (G ^ 2 - 2 * G * μ / κ + μ ^ 2 / κ ^ 2) + (2 * G / κ - 2 * μ / κ ^ 2) * S
      + (1 / κ ^ 2) * S ^ 2 := by
    intro S; simp only [hP]; field_simp; ring
  set c0 := G ^ 2 - 2 * G * μ / κ + μ ^ 2 / κ ^ 2
  set c1 := 2 * G / κ - 2 * μ / κ ^ 2
  set c2 := 1 / κ ^ 2
  have hIP : ∀ N, ∑ ω : Fin N → Fin n × Bool, (∏ i, u (ω i)) * P (∑ i, sf (ω i)) =
      c0 * q ^ N + c1 * (N * M1 * q ^ (N - 1)) +
        c2 * (N * M2 * q ^ (N - 1) + N * (N - 1 : ℝ) * M1 ^ 2 * q ^ (N - 2)) := by
    intro N
    obtain ⟨h0, h1, h2⟩ := hM N
    have hw : ∀ ω : Fin N → Fin n × Bool, (∏ i, u (ω i)) * P (∑ i, sf (ω i)) =
        c0 * (∏ i, u (ω i)) + c1 * ((∏ i, u (ω i)) * ∑ i, sf (ω i)) +
          c2 * ((∏ i, u (ω i)) * (∑ i, sf (ω i)) ^ 2) := by
      intro ω; rw [hPexp]; ring
    rw [Finset.sum_congr rfl (fun ω _ => hw ω), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h0, h1, h2]
  -- q-trick
  have hq_pow : ∀ N e, π N * q ^ (N - e) = π N := by
    intro N e
    have hqv : q = Λ / Λ := by
      simp only [hq, hu, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true,
        if_false]
      rw [hΛ, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => by ring
    by_cases hΛz : Λ = 0
    · rcases Nat.eq_zero_or_pos (N - e) with h | h
      · rw [h, pow_zero, mul_one]
      · have hN : N ≠ 0 := by omega
        have : π N = 0 := by
          simp only [hπ, ResolvingNRM.IRT.poissonPMF, hΛz, zero_mul, max_self, zero_pow hN]
          simp
        rw [this, zero_mul]
    · rw [hqv, div_self hΛz, one_pow, mul_one]
  have hΛM1 : Λ * M1 = μ := by
    by_cases hΛz : Λ = 0
    · have hall : ∀ j, lam j = 0 := by
        intro j
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hlam j).le)).mp hΛz j (Finset.mem_univ j)
      have : μ = 0 := Finset.sum_eq_zero fun j _ => absurd (hall j) (hlam j).ne'
      rw [this, hΛz, zero_mul]
    · simp only [hM1, hu, hsf, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true,
        if_false, Finset.mul_sum, hμ]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hp, ResolvingNRM.FRUpper.frProbs]
      have := (hlam j).ne'
      field_simp
      ring
  have hΛM2 : Λ * M2 = σ2 := by
    by_cases hΛz : Λ = 0
    · have hall : ∀ j, lam j = 0 := by
        intro j
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hlam j).le)).mp hΛz j (Finset.mem_univ j)
      have : σ2 = 0 := Finset.sum_eq_zero fun j _ => absurd (hall j) (hlam j).ne'
      rw [this, hΛz, zero_mul]
    · simp only [hM2, hu, hsf, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true,
        if_false, Finset.mul_sum, hσ2]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hp, ResolvingNRM.FRUpper.frProbs]
      have := (hlam j).ne'
      field_simp
      ring
  -- the termwise bound and its sum
  set R : ℕ → ℝ := fun N => c0 * π N + c1 * M1 * (π N * N) +
    c2 * (M2 * (π N * N) + M1 ^ 2 * (π N * ((N : ℝ) * ((N : ℝ) - 1)))) with hR
  have hπs := poisson_hasSum (Λ * 1)
  have hR_sum : HasSum R (c0 + c1 * M1 * Λ + c2 * (M2 * Λ + M1 ^ 2 * Λ ^ 2)) := by
    have h1 := poisson_mom1 (Λ * 1) (by linarith)
    have h2 := poisson_mom2 (Λ * 1) (by linarith)
    rw [mul_one] at h1 h2
    have := ((hπs.mul_left c0).add (h1.mul_left (c1 * M1))).add
      ((h1.mul_left M2).add (h2.mul_left (M1 ^ 2)) |>.mul_left c2)
    have hπ' : π = fun N => ResolvingNRM.IRT.poissonPMF Λ N := by simp only [hπ, mul_one]
    simp only [hR, hπ']
    simpa only [mul_one] using this
  have hterm : ∀ N, π N * ∑ ω : Fin N → Fin n × Bool, (∏ i, u (ω i)) * F (o N ω) ≤ R N := by
    intro N
    have hle : ∑ ω : Fin N → Fin n × Bool, (∏ i, u (ω i)) * F (o N ω) ≤
        ∑ ω : Fin N → Fin n × Bool, (∏ i, u (ω i)) * P (∑ i, sf (ω i)) :=
      Finset.sum_le_sum fun ω _ =>
        mul_le_mul_of_nonneg_left (hpt N ω) (Finset.prod_nonneg fun i _ => hu0 _)
    have hπ0 : 0 ≤ π N := poisson_nonneg _ _
    calc _ ≤ π N * ∑ ω : Fin N → Fin n × Bool, (∏ i, u (ω i)) * P (∑ i, sf (ω i)) :=
          mul_le_mul_of_nonneg_left hle hπ0
      _ = R N := by
        rw [hIP]
        have e0 := hq_pow N 0
        have e1 := hq_pow N 1
        have e2 := hq_pow N 2
        simp only [Nat.sub_zero] at e0
        simp only [hR]
        linear_combination c0 * e0 + (c1 * N * M1 + c2 * N * M2) * e1 +
          c2 * N * (N - 1 : ℝ) * M1 ^ 2 * e2
  have hnn : ∀ N, 0 ≤ π N * ∑ ω : Fin N → Fin n × Bool, (∏ i, u (ω i)) * F (o N ω) := fun N =>
    mul_nonneg (poisson_nonneg _ _) (Finset.sum_nonneg fun ω _ =>
      mul_nonneg (Finset.prod_nonneg fun i _ => hu0 _) (hF0 _))
  have hsumL := Summable.of_nonneg_of_le hnn hterm hR_sum.summable
  have key := Summable.tsum_le_tsum hterm hsumL hR_sum.summable
  rw [hR_sum.tsum_eq] at key
  show ResolvingNRM.FRUpper.windowExp A r lam 1 p c (fun _ c' => F c') ≤ G ^ 2 + σ2 / κ ^ 2
  rw [hE]
  refine key.trans (le_of_eq ?_)
  have e1 : M1 * Λ = μ := by rw [mul_comm]; exact hΛM1
  have e2 : M2 * Λ = σ2 := by rw [mul_comm]; exact hΛM2
  have e3 : M1 ^ 2 * Λ ^ 2 = μ ^ 2 := by rw [← e1]; ring
  rw [mul_assoc c1, e1, e2, e3]
  simp only [c0, c1, c2]
  field_simp
  ring

lemma sq_bdd (β0 : ℝ) (hβ : 0 ≤ β0) (l : Fin m) (κ : ℝ) (hκ : 0 ≤ κ) (c' : Fin m → ℝ) (hc' : 0 ≤ c') :
    0 ≤ max (β0 - c' l / κ) 0 ∧ max (β0 - c' l / κ) 0 ≤ β0 := by
  refine ⟨le_max_right _ _, max_le ?_ hβ⟩
  have : 0 ≤ c' l / κ := div_nonneg (hc' l) hκ
  linarith

/-- Quadratic shortfall along FR: the second-moment form of Lemma 8. -/
lemma quad_induction (hlam : ∀ j, 0 < lam j) (hA : ∀ l j, 0 ≤ A l j)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel)
    (l : Fin m) (β0 : ℝ) (hβ : 0 ≤ β0) :
    ∀ t k (c : Fin m → ℝ), 0 ≤ c → t + 1 ≤ k →
      ResolvingNRM.FRUpper.frStateExp A r lam sel k t
          (fun c' => (max (β0 - c' l / ((k : ℝ) - t)) 0) ^ 2) c
        ≤ (max (β0 - c l / k) 0) ^ 2 +
          ResolvingNRM.FRUpper.Kres A lam l ^ 2 * ∑ i ∈ Finset.range t, 1 / ((k : ℝ) - i - 1) ^ 2 := by
  have hK2 : ResolvingNRM.FRUpper.Kres A lam l ^ 2 = ∑ j, A l j ^ 2 * lam j := by
    unfold ResolvingNRM.FRUpper.Kres
    exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hlam j).le)
  intro t
  induction t with
  | zero =>
    intro k c hc hk
    simp [ResolvingNRM.FRUpper.frStateExp]
  | succ t ih =>
    intro k c hc hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : t + 1 ≤ k' := by omega
    have hk'pos : (0 : ℝ) < k' := by
      have : (1 : ℝ) ≤ k' := by exact_mod_cast (show 1 ≤ k' by omega)
      linarith
    set K2 := ResolvingNRM.FRUpper.Kres A lam l ^ 2 with hK2def
    set S' := ∑ i ∈ Finset.range t, 1 / ((k' : ℝ) - i - 1) ^ 2 with hS'
    set b : Fin m → ℝ := fun l => c l / ((k' + 1 : ℕ) : ℝ) with hb
    have hb0 : 0 ≤ b := fun l => div_nonneg (hc l) (Nat.cast_nonneg _)
    obtain ⟨⟨hAx, hx0, hx1⟩, -⟩ := hsel b hb0
    obtain ⟨hp0, hp1⟩ := sel_probs A r lam hlam sel hsel b hb0
    have W := window_isExp A r lam hlam _ hp0 hp1 c hc
    set g : (Fin m → ℝ) → ℝ := fun c' => (max (β0 - c' l / ((k' : ℝ) - t)) 0) ^ 2 with hg
    have hgeq : (fun c' : Fin m → ℝ => (max (β0 - c' l / (((k' + 1 : ℕ) : ℝ) - ((t + 1 : ℕ) : ℝ))) 0) ^ 2)
        = g := by
      funext c'; simp only [hg]; push_cast; ring_nf
    have hkt : (0 : ℝ) ≤ (k' : ℝ) - t := by
      have : (t : ℝ) + 1 ≤ k' := by exact_mod_cast hk'
      linarith
    have hgb : BddNN g := ⟨β0 ^ 2, fun c' hc' => by
      obtain ⟨h1, h2⟩ := sq_bdd β0 hβ l _ hkt c' hc'
      simp only [hg]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ h1 h2 2⟩
    set F : (Fin m → ℝ) → ℝ := fun c' => (max (β0 - c' l / k') 0) ^ 2 with hF
    have hFb : BddNN F := ⟨β0 ^ 2, fun c' hc' => by
      obtain ⟨h1, h2⟩ := sq_bdd β0 hβ l _ hk'pos.le c' hc'
      simp only [hF]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ h1 h2 2⟩
    have e : ResolvingNRM.FRUpper.frStateExp A r lam sel (k' + 1) (t + 1)
          (fun c' => (max (β0 - c' l / (((k' + 1 : ℕ) : ℝ) - ((t + 1 : ℕ) : ℝ))) 0) ^ 2) c =
        ResolvingNRM.FRUpper.windowExp A r lam 1 (ResolvingNRM.FRUpper.frProbs lam (sel b)) c
          (fun _ c' => ResolvingNRM.FRUpper.frStateExp A r lam sel k' t g c') := by
      rw [hgeq]; rfl
    rw [e]
    -- inner bound by the induction hypothesis
    have hin : ∀ c', 0 ≤ c' → ResolvingNRM.FRUpper.frStateExp A r lam sel k' t g c' ≤
        1 * F c' + K2 * S' * 1 := by
      intro c' hc'
      have := ih k' c' hc' hk'
      simp only [hg, hF, hK2def, hS'] at this ⊢
      linarith
    have hEb : BddNN (fun c' => ResolvingNRM.FRUpper.frStateExp A r lam sel k' t g c') := by
      obtain ⟨B, hB⟩ := hgb
      exact ⟨B, fun c' hc' => (frState_isExp A r lam hlam sel hsel t k' c' hc').bound g B hB⟩
    have step1 := W.mono _ (fun c' => 1 * F c' + K2 * S' * (fun _ => (1 : ℝ)) c') hEb
      (bddNN_lin hFb (bddNN_const 1) 1 (K2 * S')) hin
    rw [W.lin F (fun _ => (1 : ℝ)) hFb (bddNN_const 1) 1 (K2 * S'), W.const 1] at step1
    -- the one-window bound
    have hq := window_quad A r lam hlam hA (sel b) hx0 hx1 c hc (k' : ℝ) hk'pos β0 hβ l
    have hμ : ∑ j, A l j * sel b j ≤ c l / ((k' : ℝ) + 1) := by
      have := hAx l
      simp only [Matrix.mulVec, dotProduct] at this
      calc _ ≤ b l := this
        _ = _ := by simp only [hb]; push_cast; ring
    have hm : c l / ((k' : ℝ) + 1) ≤ (c l - ∑ j, A l j * sel b j) / k' := by
      rw [le_div_iff₀ hk'pos]
      have h1 : c l / ((k' : ℝ) + 1) * k' = c l - c l / ((k' : ℝ) + 1) := by
        field_simp; ring
      rw [h1]; linarith
    have hG : (max (β0 - (c l - ∑ j, A l j * sel b j) / k') 0) ^ 2 ≤
        (max (β0 - c l / ((k' + 1 : ℕ) : ℝ)) 0) ^ 2 := by
      apply pow_le_pow_left₀ (le_max_right _ _)
      push_cast
      exact max_le_max (by linarith) (le_refl _)
    have hσ : (∑ j, A l j ^ 2 * sel b j) / (k' : ℝ) ^ 2 ≤ K2 * (1 / ((k' : ℝ)) ^ 2) := by
      rw [hK2, mul_one_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx1 j) (sq_nonneg _)
    have hsum : ∑ i ∈ Finset.range (t + 1), 1 / (((k' + 1 : ℕ) : ℝ) - i - 1) ^ 2 =
        S' + 1 / ((k' : ℝ)) ^ 2 := by
      rw [Finset.sum_range_succ', hS']
      push_cast
      congr 1
      · refine Finset.sum_congr rfl fun i _ => by ring_nf
      · ring_nf
    rw [hsum]
    have hF' : ResolvingNRM.FRUpper.windowExp A r lam 1 (ResolvingNRM.FRUpper.frProbs lam (sel b)) c
        (fun _ c' => F c') = ResolvingNRM.FRUpper.windowExp A r lam 1
          (ResolvingNRM.FRUpper.frProbs lam (sel b)) c
          (fun _ c' => (max (β0 - c' l / k') 0) ^ 2) := rfl
    have := step1
    rw [hF'] at this
    calc _ ≤ _ := this
      _ ≤ _ := by nlinarith [hq, hG, hσ]

end FRGapAux

open FRGapAux in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel)
    (T t : ℕ) (ht : t + 1 ≤ T) (C : Fin m → ℝ) (hC : 0 ≤ C) (l : Fin m) :
    ResolvingNRM.FRUpper.frStateExp A r lam sel T t (fun c => max (C l / T - c l / ((T : ℝ) - t)) 0) C
      ≤ ResolvingNRM.FRUpper.Kres A lam l *
          Real.sqrt (∑ i ∈ Finset.range t, 1 / ((T : ℝ) - i - 1) ^ 2) := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hβ : 0 ≤ C l / T := div_nonneg (hC l) hT.le
  have hkt : (0 : ℝ) ≤ (T : ℝ) - t := by
    have : (t : ℝ) + 1 ≤ T := by exact_mod_cast ht
    linarith
  set E := fun g => ResolvingNRM.FRUpper.frStateExp A r lam sel T t g C with hEdef
  have hE : IsExp E := frState_isExp A r lam hlam sel hsel t T C hC
  set X : (Fin m → ℝ) → ℝ := fun c => max (C l / T - c l / ((T : ℝ) - t)) 0 with hX
  set S := ∑ i ∈ Finset.range t, 1 / ((T : ℝ) - i - 1) ^ 2 with hS
  set K := ResolvingNRM.FRUpper.Kres A lam l with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hXb : BddNN X := ⟨C l / T, fun c hc => by
    obtain ⟨h1, h2⟩ := sq_bdd (C l / T) hβ l _ hkt c hc
    simp only [hX]; rw [abs_of_nonneg h1]; exact h2⟩
  have hX2b : BddNN (fun c => X c ^ 2) := ⟨(C l / T) ^ 2, fun c hc => by
    obtain ⟨h1, h2⟩ := sq_bdd (C l / T) hβ l _ hkt c hc
    simp only [hX]; rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ h1 h2 2⟩
  -- second moment
  have h2 : E (fun c => X c ^ 2) ≤ K ^ 2 * S := by
    have := quad_induction A r lam hlam hA sel hsel l (C l / T) hβ t T C hC ht
    simp only [sub_self, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_add] at this
    exact this
  -- Jensen: (E X)^2 ≤ E X^2
  set a := E X with ha
  have hlin1 := hE.lin (fun c => X c ^ 2) X hX2b hXb 1 (-2 * a)
  have hb1 := bddNN_lin hX2b hXb 1 (-2 * a)
  have hlin2 := hE.lin (fun c => 1 * X c ^ 2 + -2 * a * X c) (fun _ => (1 : ℝ)) hb1 (bddNN_const 1)
    1 (a ^ 2)
  rw [hlin1, hE.const] at hlin2
  have hpos := hE.mono (fun _ => (0 : ℝ))
    (fun c => 1 * (1 * X c ^ 2 + -2 * a * X c) + a ^ 2 * 1) (bddNN_const 0)
    (bddNN_lin hb1 (bddNN_const 1) 1 (a ^ 2)) (fun c _ => by nlinarith [sq_nonneg (X c - a)])
  rw [hE.const, hlin2] at hpos
  have hsq : a ^ 2 ≤ K ^ 2 * S := by nlinarith
  have : a ≤ Real.sqrt (K ^ 2 * S) := by
    calc a ≤ |a| := le_abs_self a
      _ = Real.sqrt (a ^ 2) := (Real.sqrt_sq_eq_abs a).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK0] at this
  exact this
