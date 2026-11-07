-- Prove2me | solution 1 for ResolvingNRM.FRUpper.fr_revenue_accounting
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:34:32.237989+00:00
-- url     : https://prove2.me/submissions/82f00722-baec-4654-bf8a-f1253208b2ec

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

lemma IsExp.sum_on {m : ℕ} {ι : Type*} {E : ((Fin m → ℝ) → ℝ) → ℝ} (hE : IsExp E)
    (s : Finset ι) (f : ι → (Fin m → ℝ) → ℝ) (hf : ∀ i ∈ s, BddNN (f i)) :
    BddNN (fun c => ∑ i ∈ s, f i c) ∧ E (fun c => ∑ i ∈ s, f i c) = ∑ i ∈ s, E (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨bddNN_const 0, hE.const 0⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    obtain ⟨hb, he⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hfi := hf i (Finset.mem_insert_self i s)
    have key := hE.lin (f i) (fun c => ∑ i ∈ s, f i c) hfi hb 1 1
    simp only [one_mul] at key
    refine ⟨?_, ?_⟩
    · have := bddNN_lin hfi hb 1 1
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


lemma runWindow_append : ∀ (L L' : List (Fin n × Bool)) (c : Fin m → ℝ),
    ResolvingNRM.IRT.runWindow A r (L ++ L') c =
      ((ResolvingNRM.IRT.runWindow A r L c).1 +
          (ResolvingNRM.IRT.runWindow A r L' (ResolvingNRM.IRT.runWindow A r L c).2).1,
        (ResolvingNRM.IRT.runWindow A r L' (ResolvingNRM.IRT.runWindow A r L c).2).2)
  | [], L', c => by simp [ResolvingNRM.IRT.runWindow]
  | (j, b) :: rest, L', c => by
      simp only [List.cons_append, ResolvingNRM.IRT.runWindow]
      by_cases h : b = true ∧ ∀ l, A l j ≤ c l
      · rw [if_pos h, if_pos h, runWindow_append rest L']
        simp only [add_assoc]
      · rw [if_neg h, if_neg h]
        exact runWindow_append rest L' c

variable {A} in
lemma runWindow_le (hA : ∀ l j, 0 ≤ A l j) : ∀ (L : List (Fin n × Bool)) (c : Fin m → ℝ),
    (ResolvingNRM.IRT.runWindow A r L c).2 ≤ c
  | [], c => by simp [ResolvingNRM.IRT.runWindow]
  | (j, b) :: rest, c => by
      simp only [ResolvingNRM.IRT.runWindow]
      by_cases h : b = true ∧ ∀ l, A l j ≤ c l
      · rw [if_pos h]
        refine (runWindow_le hA rest _).trans fun l => ?_
        have := hA l j
        linarith
      · rw [if_neg h]
        exact runWindow_le hA rest c

lemma sum_snoc {α : Type*} [Fintype α] (N : ℕ) (F : (Fin (N+1) → α) → ℝ) :
    ∑ ω, F ω = ∑ ω' : Fin N → α, ∑ a, F (Fin.snoc ω' a) := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv fun _ => α) _ _ (fun _ => rfl)).symm

lemma ofFn_snoc {α : Type*} (N : ℕ) (ω' : Fin N → α) (a : α) :
    List.ofFn (Fin.snoc ω' a : Fin (N + 1) → α) = List.ofFn ω' ++ [a] := by
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]

/-- Class `j` can still be accepted at capacity `c`. -/
noncomputable def alive (j : Fin n) (c : Fin m → ℝ) : ℝ := if ∀ l, A l j ≤ c l then 1 else 0

variable {A} in
lemma alive_anti (j : Fin n) {c c' : Fin m → ℝ} (h : c' ≤ c) : alive A j c' ≤ alive A j c := by
  unfold alive
  by_cases h1 : ∀ l, A l j ≤ c' l
  · rw [if_pos h1, if_pos fun l => (h1 l).trans (h l)]
  · rw [if_neg h1]; split_ifs <;> norm_num

lemma alive_nonneg (j : Fin n) (c : Fin m → ℝ) : 0 ≤ alive A j c := by
  unfold alive; split_ifs <;> norm_num

lemma alive_le_one (j : Fin n) (c : Fin m → ℝ) : alive A j c ≤ 1 := by
  unfold alive; split_ifs <;> norm_num

/-- Revenue of one FR window: it is at least `∑_j r_j x_j P(class j still open at the end)`. -/
lemma window_rev (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j) (x : Fin n → ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ lam) (c : Fin m → ℝ) (hc : 0 ≤ c) :
    ∃ Wr : ℝ, 0 ≤ Wr ∧ Wr ≤ ∑ j, r j * x j ∧
      (∑ j, r j * x j * ResolvingNRM.FRUpper.windowExp A r lam 1
          (ResolvingNRM.FRUpper.frProbs lam x) c (fun _ c' => alive A j c')) ≤ Wr ∧
      ∀ G : (Fin m → ℝ) → ℝ, BddNN G →
        ResolvingNRM.FRUpper.windowExp A r lam 1 (ResolvingNRM.FRUpper.frProbs lam x) c
          (fun rev c' => rev + G c') =
        Wr + ResolvingNRM.FRUpper.windowExp A r lam 1 (ResolvingNRM.FRUpper.frProbs lam x) c
          (fun _ c' => G c') := by
  set p := ResolvingNRM.FRUpper.frProbs lam x with hp
  set Λ := ∑ j, lam j with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun j _ => (hlam j).le
  have hp0 : 0 ≤ p := fun j => div_nonneg (hx0 j) (hlam j).le
  have hp1 : p ≤ 1 := fun j => div_le_one_of_le₀ (hx1 j) (hlam j).le
  have hrj : ∀ j, 0 ≤ r j := fun j => hr j
  have hrx : 0 ≤ ∑ j, r j * x j := Finset.sum_nonneg fun j _ => mul_nonneg (hrj j) (hx0 j)
  set π : ℕ → ℝ := fun N => ResolvingNRM.IRT.poissonPMF (Λ * 1) N with hπ
  have hπ0 : ∀ N, 0 ≤ π N := fun N => poisson_nonneg _ _
  have hπs : HasSum π 1 := poisson_hasSum _
  set u : Fin n × Bool → ℝ := fun a => (lam a.1 / Λ) * (if a.2 then p a.1 else 1 - p a.1) with hu
  have hu0 : ∀ a, 0 ≤ u a := by
    intro a
    apply mul_nonneg (div_nonneg (hlam _).le hΛ0)
    split_ifs
    · exact hp0 _
    · have := hp1 a.1; simp only [Pi.one_apply] at this; linarith
  set w : (N : ℕ) → (Fin N → Fin n × Bool) → ℝ := fun N ω => ∏ i, u (ω i) with hw
  have hw0 : ∀ N ω, 0 ≤ w N ω := fun N ω => Finset.prod_nonneg fun i _ => hu0 _
  set run : (N : ℕ) → (Fin N → Fin n × Bool) → ℝ × (Fin m → ℝ) := fun N ω =>
    ResolvingNRM.IRT.runWindow A r (List.ofFn ω) c with hrun
  have hconv : ∀ F : ℝ → (Fin m → ℝ) → ℝ, ResolvingNRM.FRUpper.windowExp A r lam 1 p c F =
      ∑' N, π N * ∑ ω : Fin N → Fin n × Bool, w N ω * F (run N ω).1 (run N ω).2 := by
    intro F
    unfold ResolvingNRM.FRUpper.windowExp
    refine tsum_congr fun N => ?_
    congr 1
    rw [sum_cls_coin]
  have hrun0 : run 0 Fin.elim0 = (0, c) := by
    simp [hrun, ResolvingNRM.IRT.runWindow]
  have hsum0 : ∀ H : (Fin 0 → Fin n × Bool) → ℝ, ∑ ω : Fin 0 → Fin n × Bool, H ω = H Fin.elim0 := by
    intro H
    rw [Fintype.sum_unique]
    congr 1
  by_cases hΛz : Λ = 0
  · -- no customer classes: the window is empty
    have hall : ∀ j, lam j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hlam j).le)).mp hΛz j (Finset.mem_univ j)
    have hπN : ∀ N, N ≠ 0 → π N = 0 := by
      intro N hN
      simp only [hπ, ResolvingNRM.IRT.poissonPMF, hΛz, zero_mul, max_self, zero_pow hN]
      simp
    have hW : ∀ F : ℝ → (Fin m → ℝ) → ℝ, ResolvingNRM.FRUpper.windowExp A r lam 1 p c F = F 0 c := by
      intro F
      rw [hconv, tsum_eq_single 0 (fun N hN => by rw [hπN N hN, zero_mul])]
      rw [hsum0, hrun0]
      simp [hπ, ResolvingNRM.IRT.poissonPMF, hΛz, hw]
    refine ⟨0, le_refl _, hrx, ?_, ?_⟩
    · rw [Finset.sum_eq_zero fun j _ => absurd (hall j) (hlam j).ne']
    · intro G _
      rw [hW, hW, zero_add]
  · -- the main case
    have hq : ∑ a, u a = 1 := by
      simp only [hu, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
      have : ∀ j, lam j / Λ * p j + lam j / Λ * (1 - p j) = lam j / Λ := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_div]
      exact div_self hΛz
    have hmass : ∀ N, ∑ ω : Fin N → Fin n × Bool, w N ω = 1 := by
      intro N
      rw [(moments u u N).1, hq, one_pow]
    set κ : Fin n → ℝ := fun j => lam j / Λ * p j * r j with hκ
    have hκ0 : ∀ j, 0 ≤ κ j := fun j =>
      mul_nonneg (mul_nonneg (div_nonneg (hlam j).le hΛ0) (hp0 j)) (hrj j)
    have hΛκ : ∀ j, Λ * κ j = r j * x j := by
      intro j
      simp only [hκ, hp, ResolvingNRM.FRUpper.frProbs]
      have := (hlam j).ne'
      field_simp
    set R : ℕ → ℝ := fun N => ∑ ω : Fin N → Fin n × Bool, w N ω * (run N ω).1 with hR
    set e : Fin n → ℕ → ℝ := fun j N => ∑ ω : Fin N → Fin n × Bool, w N ω * alive A j (run N ω).2
      with he
    have hw_snoc : ∀ N (ω' : Fin N → Fin n × Bool) a, w (N + 1) (Fin.snoc ω' a) = w N ω' * u a := by
      intro N ω' a
      simp only [hw, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    have hrun_snoc : ∀ N (ω' : Fin N → Fin n × Bool) a, run (N + 1) (Fin.snoc ω' a) =
        ((run N ω').1 + (ResolvingNRM.IRT.runWindow A r [a] (run N ω').2).1,
          (ResolvingNRM.IRT.runWindow A r [a] (run N ω').2).2) := by
      intro N ω' a
      simp only [hrun, ofFn_snoc, runWindow_append]
    have hone : ∀ c' : Fin m → ℝ, ∑ a, u a * (ResolvingNRM.IRT.runWindow A r [a] c').1 =
        ∑ j, κ j * alive A j c' := by
      intro c'
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Fintype.sum_bool, hu, hκ, alive, ResolvingNRM.IRT.runWindow]
      by_cases h : ∀ l, A l j ≤ c' l
      · simp [h]; try ring
      · simp [h]
    have hRs : ∀ N, R (N + 1) = R N + ∑ j, κ j * e j N := by
      intro N
      simp only [hR, he]
      rw [sum_snoc]
      have : ∀ ω' : Fin N → Fin n × Bool, ∑ a, w (N + 1) (Fin.snoc ω' a) * (run (N + 1) (Fin.snoc ω' a)).1
          = w N ω' * (run N ω').1 + ∑ j, κ j * (w N ω' * alive A j (run N ω').2) := by
        intro ω'
        simp only [hw_snoc, hrun_snoc]
        have h1 := hone (run N ω').2
        have h2 : ∑ a, w N ω' * u a * ((run N ω').1 + (ResolvingNRM.IRT.runWindow A r [a] (run N ω').2).1)
            = w N ω' * (run N ω').1 * ∑ a, u a +
              w N ω' * ∑ a, u a * (ResolvingNRM.IRT.runWindow A r [a] (run N ω').2).1 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => by ring
        rw [h2, hq, h1, Finset.mul_sum]
        simp only [mul_one]
        congr 1
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [Finset.sum_congr rfl fun ω' _ => this ω', Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    have hes : ∀ j N, e j (N + 1) ≤ e j N := by
      intro j N
      simp only [he]
      rw [sum_snoc]
      refine Finset.sum_le_sum fun ω' _ => ?_
      simp only [hw_snoc, hrun_snoc]
      calc ∑ a, w N ω' * u a * alive A j (ResolvingNRM.IRT.runWindow A r [a] (run N ω').2).2
          ≤ ∑ a, w N ω' * u a * alive A j (run N ω').2 :=
            Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
              (alive_anti j (runWindow_le r hA _ _)) (mul_nonneg (hw0 N ω') (hu0 a))
        _ = w N ω' * alive A j (run N ω').2 := by
            rw [← Finset.sum_mul, ← Finset.mul_sum, hq, mul_one]
    have he0 : ∀ j N, 0 ≤ e j N := fun j N =>
      Finset.sum_nonneg fun ω _ => mul_nonneg (hw0 N ω) (alive_nonneg A j _)
    have he1 : ∀ j N, e j N ≤ 1 := by
      intro j N
      calc e j N ≤ ∑ ω : Fin N → Fin n × Bool, w N ω * 1 :=
            Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (alive_le_one A j _) (hw0 N ω)
        _ = 1 := by simp only [mul_one]; exact hmass N
    have hR0 : R 0 = 0 := by simp only [hR]; rw [hsum0, hrun0]; simp
    have hRnn : ∀ N, 0 ≤ R N := by
      intro N
      induction N with
      | zero => rw [hR0]
      | succ N ih =>
        rw [hRs]
        exact add_nonneg ih (Finset.sum_nonneg fun j _ => mul_nonneg (hκ0 j) (he0 j N))
    have hRup : ∀ N, R N ≤ N * ∑ j, κ j := by
      intro N
      induction N with
      | zero => rw [hR0]; simp
      | succ N ih =>
        rw [hRs]
        have : ∑ j, κ j * e j N ≤ ∑ j, κ j := Finset.sum_le_sum fun j _ => by
          have := he1 j N; have := hκ0 j; nlinarith
        push_cast
        linarith
    have hRlow : ∀ N : ℕ, ((N : ℝ) + 1) * ∑ j, κ j * e j N ≤ R (N + 1) := by
      intro N
      induction N with
      | zero => rw [hRs, hR0]; simp
      | succ N ih =>
        rw [hRs (N + 1)]
        have : ∑ j, κ j * e j (N + 1) ≤ ∑ j, κ j * e j N := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hes j N) (hκ0 j)
        push_cast
        nlinarith
    -- summability
    have hm1 := poisson_mom1 (Λ * 1) (by linarith)
    have hRsum : Summable fun N => π N * R N := by
      refine Summable.of_nonneg_of_le (fun N => mul_nonneg (hπ0 N) (hRnn N)) (fun N => ?_)
        ((hm1.mul_left (∑ j, κ j)).summable)
      have := mul_le_mul_of_nonneg_left (hRup N) (hπ0 N)
      linarith
    have hIsum : ∀ G : (Fin m → ℝ) → ℝ, BddNN G →
        Summable fun N => π N * ∑ ω : Fin N → Fin n × Bool, w N ω * G (run N ω).2 := by
      rintro G ⟨B, hB⟩
      refine Summable.of_norm_bounded (hπs.summable.mul_left B) fun N => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ0 N)]
      have : |∑ ω : Fin N → Fin n × Bool, w N ω * G (run N ω).2| ≤ B := by
        calc _ ≤ ∑ ω : Fin N → Fin n × Bool, |w N ω * G (run N ω).2| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ ω : Fin N → Fin n × Bool, w N ω * B := Finset.sum_le_sum fun ω _ => by
              rw [abs_mul, abs_of_nonneg (hw0 N ω)]
              exact mul_le_mul_of_nonneg_left (hB _ (runWindow_nonneg A r _ c hc)) (hw0 N ω)
          _ = B := by rw [← Finset.sum_mul, hmass, one_mul]
      have := mul_le_mul_of_nonneg_left this (hπ0 N)
      linarith
    refine ⟨∑' N, π N * R N, tsum_nonneg fun N => mul_nonneg (hπ0 N) (hRnn N), ?_, ?_, ?_⟩
    · -- upper bound
      have h1 := Summable.tsum_le_tsum (fun N => by
          have := mul_le_mul_of_nonneg_left (hRup N) (hπ0 N)
          show π N * R N ≤ (∑ j, κ j) * (ResolvingNRM.IRT.poissonPMF (Λ * 1) N * N)
          simp only [hπ] at this ⊢; linarith) hRsum (hm1.mul_left (∑ j, κ j)).summable
      rw [(hm1.mul_left _).tsum_eq] at h1
      calc _ ≤ _ := h1
        _ = ∑ j, r j * x j := by
          rw [mul_one, Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by rw [mul_comm, hΛκ]
    · -- lower bound
      have hes_sum : ∀ j, HasSum (fun N => π N * e j N)
          (ResolvingNRM.FRUpper.windowExp A r lam 1 p c (fun _ c' => alive A j c')) := by
        intro j
        rw [hconv]
        have hs : Summable fun N => π N * e j N :=
          Summable.of_nonneg_of_le (fun N => mul_nonneg (hπ0 N) (he0 j N))
            (fun N => by have := he1 j N; have := hπ0 N; nlinarith) hπs.summable
        exact hs.hasSum
      have hg : HasSum (fun N => ∑ j, r j * x j * (π N * e j N))
          (∑ j, r j * x j * ResolvingNRM.FRUpper.windowExp A r lam 1 p c (fun _ c' => alive A j c')) :=
        hasSum_sum fun j _ => (hes_sum j).mul_left _
      have hf : HasSum (fun N => π (N + 1) * R (N + 1)) (∑' N, π N * R N) := by
        have := (hasSum_nat_add_iff' 1).mpr hRsum.hasSum
        simpa [hR0] using this
      refine hasSum_le (fun N => ?_) hg hf
      have hsucc := poisson_succ (Λ * 1) (by linarith) N
      have := mul_le_mul_of_nonneg_left (hRlow N) (hπ0 (N + 1))
      calc ∑ j, r j * x j * (π N * e j N) = (Λ * 1) * π N * ∑ j, κ j * e j N := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← hΛκ j]; ring
        _ = π (N + 1) * (((N : ℝ) + 1) * ∑ j, κ j * e j N) := by
            simp only [hπ]; rw [← hsucc]; ring
        _ ≤ _ := this
    · intro G hG
      rw [hconv, hconv]
      simp only [mul_add, Finset.sum_add_distrib]
      exact Summable.tsum_add hRsum (hIsum G hG)

variable {A} in
lemma window_dead (hA : ∀ l j, 0 ≤ A l j) (p : Fin n → ℝ) (c : Fin m → ℝ) (j : Fin n)
    (hj : alive A j c = 0) :
    ResolvingNRM.FRUpper.windowExp A r lam 1 p c (fun _ c' => alive A j c') = 0 := by
  have h0 : ∀ L, alive A j (ResolvingNRM.IRT.runWindow A r L c).2 = 0 := fun L =>
    le_antisymm (by have := alive_anti (A := A) j (runWindow_le r hA L c); linarith) (alive_nonneg A j _)
  unfold ResolvingNRM.FRUpper.windowExp
  simp only [h0, mul_zero, Finset.sum_const_zero, tsum_zero]

lemma frTail_bdd (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel) :
    ∀ k (c : Fin m → ℝ), 0 ≤ c →
      0 ≤ ResolvingNRM.FRUpper.frTail A r lam sel k c ∧
        ResolvingNRM.FRUpper.frTail A r lam sel k c ≤ k * ∑ j, r j * lam j := by
  intro k
  induction k with
  | zero => intro c _; simp [ResolvingNRM.FRUpper.frTail]
  | succ k ih =>
    intro c hc
    set b : Fin m → ℝ := fun l => c l / ((k : ℝ) + 1) with hb
    have hb0 : 0 ≤ b := fun l => div_nonneg (hc l) (by positivity)
    obtain ⟨⟨-, hx0, hx1⟩, -⟩ := hsel b hb0
    obtain ⟨hp0, hp1⟩ := sel_probs A r lam hlam sel hsel b hb0
    have W := window_isExp A r lam hlam _ hp0 hp1 c hc
    obtain ⟨Wr, hW0, hW1, -, hsplit⟩ := window_rev A r lam hlam hr hA (sel b) hx0 hx1 c hc
    have hB : BddNN (ResolvingNRM.FRUpper.frTail A r lam sel k) := ⟨k * ∑ j, r j * lam j, fun c' hc' => by
      obtain ⟨h1, h2⟩ := ih c' hc'
      rw [abs_of_nonneg h1]; exact h2⟩
    have e : ResolvingNRM.FRUpper.frTail A r lam sel (k + 1) c =
        ResolvingNRM.FRUpper.windowExp A r lam 1 (ResolvingNRM.FRUpper.frProbs lam (sel b)) c
          (fun rev c' => rev + ResolvingNRM.FRUpper.frTail A r lam sel k c') := rfl
    rw [e, hsplit _ hB]
    have hlo := W.mono (fun _ => (0 : ℝ)) _ (bddNN_const 0) hB (fun c' hc' => (ih c' hc').1)
    have hhi := W.mono _ (fun _ => (k : ℝ) * ∑ j, r j * lam j) hB (bddNN_const _)
      (fun c' hc' => (ih c' hc').2)
    rw [W.const] at hlo hhi
    have hrx : ∑ j, r j * sel b j ≤ ∑ j, r j * lam j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx1 j) (hr j)
    push_cast
    constructor
    · linarith
    · nlinarith

/-- `∑_{t<k} E[r ⬝ x(t)]` along FR with `k` periods to go. -/
noncomputable def Phi (sel : (Fin m → ℝ) → (Fin n → ℝ)) (k : ℕ) (c : Fin m → ℝ) : ℝ :=
  ∑ t ∈ Finset.range k, ResolvingNRM.FRUpper.frStateExp A r lam sel k t
    (fun c' => r ⬝ᵥ sel (fun l => c' l / ((k : ℝ) - t))) c

lemma Phi_bdd (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel) (k : ℕ) :
    BddNN (Phi A r lam sel k) := by
  refine ⟨k * (r ⬝ᵥ lam), fun c hc => ?_⟩
  unfold Phi
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ t ∈ Finset.range k, |ResolvingNRM.FRUpper.frStateExp A r lam sel k t
      (fun c' => r ⬝ᵥ sel (fun l => c' l / ((k : ℝ) - t))) c| ≤ r ⬝ᵥ lam := by
    intro t ht
    have htk : (0 : ℝ) ≤ (k : ℝ) - t := by
      have : (t : ℝ) < k := by exact_mod_cast Finset.mem_range.mp ht
      linarith
    apply (frState_isExp A r lam hlam sel hsel t k c hc).bound
    intro c' hc'
    have hb' : 0 ≤ (fun l => c' l / ((k : ℝ) - t)) := fun l => div_nonneg (hc' l) htk
    obtain ⟨⟨-, h0, h1⟩, -⟩ := hsel _ hb'
    simp only [dotProduct]
    rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hr j) (h0 j))]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h1 j) (hr j)
  calc _ ≤ ∑ t ∈ Finset.range k, r ⬝ᵥ lam := Finset.sum_le_sum this
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma Phi_succ (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel) (k : ℕ)
    (c : Fin m → ℝ) (hc : 0 ≤ c) :
    Phi A r lam sel (k + 1) c = r ⬝ᵥ sel (fun l => c l / ((k : ℝ) + 1)) +
      ResolvingNRM.FRUpper.windowExp A r lam 1
        (ResolvingNRM.FRUpper.frProbs lam (sel fun l => c l / ((k : ℝ) + 1))) c
        (fun _ c' => Phi A r lam sel k c') := by
  set b : Fin m → ℝ := fun l => c l / ((k : ℝ) + 1) with hb
  have hb0 : 0 ≤ b := fun l => div_nonneg (hc l) (by positivity)
  obtain ⟨hp0, hp1⟩ := sel_probs A r lam hlam sel hsel b hb0
  have W := window_isExp A r lam hlam _ hp0 hp1 c hc
  unfold Phi
  rw [Finset.sum_range_succ']
  have e0 : ResolvingNRM.FRUpper.frStateExp A r lam sel (k + 1) 0
      (fun c' => r ⬝ᵥ sel (fun l => c' l / (((k + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)))) c =
      r ⬝ᵥ sel b := by
    simp only [ResolvingNRM.FRUpper.frStateExp, hb]
    congr 2; funext l; push_cast; ring
  have et : ∀ t ∈ Finset.range k, ResolvingNRM.FRUpper.frStateExp A r lam sel (k + 1) (t + 1)
      (fun c' => r ⬝ᵥ sel (fun l => c' l / (((k + 1 : ℕ) : ℝ) - ((t + 1 : ℕ) : ℝ)))) c =
      ResolvingNRM.FRUpper.windowExp A r lam 1 (ResolvingNRM.FRUpper.frProbs lam (sel b)) c
        (fun _ c' => ResolvingNRM.FRUpper.frStateExp A r lam sel k t
          (fun c' => r ⬝ᵥ sel (fun l => c' l / ((k : ℝ) - t))) c') := by
    intro t _
    have hkt : ((k + 1 : ℕ) : ℝ) - ((t + 1 : ℕ) : ℝ) = (k : ℝ) - t := by push_cast; ring
    have hkb : (fun l => c l / ((k + 1 : ℕ) : ℝ)) = b := by
      funext l; simp only [hb]; push_cast; ring
    simp only [hkt]
    show ResolvingNRM.FRUpper.windowExp A r lam 1
        (ResolvingNRM.FRUpper.frProbs lam (sel fun l => c l / ((k + 1 : ℕ) : ℝ))) c _ = _
    rw [hkb]
    rfl
  rw [e0, Finset.sum_congr rfl et, add_comm]
  congr 1
  have hbd : ∀ t ∈ Finset.range k, BddNN (fun c' => ResolvingNRM.FRUpper.frStateExp A r lam sel k t
      (fun c' => r ⬝ᵥ sel (fun l => c' l / ((k : ℝ) - t))) c') := by
    intro t ht
    refine ⟨r ⬝ᵥ lam, fun c' hc' => ?_⟩
    have htk : (0 : ℝ) ≤ (k : ℝ) - t := by
      have : (t : ℝ) < k := by exact_mod_cast Finset.mem_range.mp ht
      linarith
    apply (frState_isExp A r lam hlam sel hsel t k c' hc').bound
    intro c'' hc''
    have hb' : 0 ≤ (fun l => c'' l / ((k : ℝ) - t)) := fun l => div_nonneg (hc'' l) htk
    obtain ⟨⟨-, h0, h1⟩, -⟩ := hsel _ hb'
    simp only [dotProduct]
    rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hr j) (h0 j))]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h1 j) (hr j)
  exact ((W.sum_on (Finset.range k) _ hbd).2).symm

/-- The partial harmonic sums `H_k = ∑_{i<k} 1/(i+1)`. -/
noncomputable def Hk (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 1)

/-- The accounting invariant behind Eq. (32). -/
lemma acc_inv (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel) :
    ∀ k (c : Fin m → ℝ), 0 ≤ c →
      Phi A r lam sel k c - (∑ j, r j) * Hk k - ∑ j, r j * lam j * alive A j c
        ≤ ResolvingNRM.FRUpper.frTail A r lam sel k c := by
  have hrj : ∀ j, 0 ≤ r j := fun j => hr j
  intro k
  induction k with
  | zero =>
    intro c _
    simp only [Phi, Hk, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero,
      ResolvingNRM.FRUpper.frTail, zero_sub, neg_nonpos]
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hrj j) (hlam j).le) (alive_nonneg A j c)
  | succ k ih =>
    intro c hc
    set b : Fin m → ℝ := fun l => c l / ((k : ℝ) + 1) with hb
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hb0 : 0 ≤ b := fun l => div_nonneg (hc l) hk1.le
    obtain ⟨⟨hAx, hx0, hx1⟩, -⟩ := hsel b hb0
    obtain ⟨hp0, hp1⟩ := sel_probs A r lam hlam sel hsel b hb0
    have W := window_isExp A r lam hlam _ hp0 hp1 c hc
    obtain ⟨Wr, -, -, hWlow, hsplit⟩ := window_rev A r lam hlam hr hA (sel b) hx0 hx1 c hc
    set x := sel b with hx
    set Wf := fun G : (Fin m → ℝ) → ℝ =>
      ResolvingNRM.FRUpper.windowExp A r lam 1 (ResolvingNRM.FRUpper.frProbs lam x) c
        (fun _ c' => G c') with hWf
    have hB : BddNN (ResolvingNRM.FRUpper.frTail A r lam sel k) := ⟨k * ∑ j, r j * lam j, fun c' hc' => by
      obtain ⟨h1, h2⟩ := frTail_bdd A r lam hlam hr hA sel hsel k c' hc'
      rw [abs_of_nonneg h1]; exact h2⟩
    have e : ResolvingNRM.FRUpper.frTail A r lam sel (k + 1) c =
        ResolvingNRM.FRUpper.windowExp A r lam 1 (ResolvingNRM.FRUpper.frProbs lam x) c
          (fun rev c' => rev + ResolvingNRM.FRUpper.frTail A r lam sel k c') := rfl
    rw [e, hsplit _ hB, Phi_succ A r lam hlam hr sel hsel k c hc]
    -- lower function
    have hal : ∀ j, BddNN (alive A j) := fun j => ⟨1, fun c' _ => by
      rw [abs_of_nonneg (alive_nonneg A j c')]; exact alive_le_one A j c'⟩
    set M : (Fin m → ℝ) → ℝ := fun c' => ∑ j, r j * lam j * alive A j c' with hM
    have hMs := W.sum Finset.univ (fun j => r j * lam j) (fun j => alive A j) hal
    set D : ℝ := (∑ j, r j) * Hk k with hD
    have hMD : BddNN (fun c' => 1 * M c' + D * (fun _ => (1 : ℝ)) c') :=
      bddNN_lin hMs.1 (bddNN_const 1) 1 D
    have hPb := Phi_bdd A r lam hlam hr sel hsel k
    have hmono := W.mono (fun c' => 1 * Phi A r lam sel k c' + (-1) * (1 * M c' + D * (fun _ => (1 : ℝ)) c'))
      (ResolvingNRM.FRUpper.frTail A r lam sel k) (bddNN_lin hPb hMD 1 (-1)) hB
      (fun c' hc' => by have := ih c' hc'; simp only [hM, hD] at this ⊢; linarith)
    rw [W.lin _ _ hPb hMD 1 (-1), W.lin _ _ hMs.1 (bddNN_const 1) 1 D, W.const, hMs.2] at hmono
    -- per-class inequality
    have hper : ∀ j, r j * x j - r j / ((k : ℝ) + 1) - r j * lam j * alive A j c ≤
        r j * x j * Wf (alive A j) - r j * lam j * Wf (alive A j) := by
      intro j
      by_cases hj : ∀ l, A l j ≤ c l
      · have ha : alive A j c = 1 := by simp [alive, hj]
        have hWa : Wf (alive A j) ≤ 1 := by
          have := W.bound (alive A j) 1 (fun c' _ => by
            rw [abs_of_nonneg (alive_nonneg A j c')]; exact alive_le_one A j c')
          exact (le_abs_self _).trans this
        rw [ha]
        have h1 : 0 ≤ r j * (lam j - x j) * (1 - Wf (alive A j)) :=
          mul_nonneg (mul_nonneg (hrj j) (by linarith [hx1 j])) (by linarith)
        have h2 : 0 ≤ r j / ((k : ℝ) + 1) := div_nonneg (hrj j) hk1.le
        nlinarith
      · have ha : alive A j c = 0 := by simp [alive, hj]
        have hW0 : Wf (alive A j) = 0 := window_dead r lam hA _ c j ha
        rw [ha, hW0]
        push_neg at hj
        obtain ⟨l, hl⟩ := hj
        have hApos : 0 < A l j := lt_of_le_of_lt (hc l) hl
        have h1 : A l j * x j ≤ ∑ i, A l i * x i :=
          Finset.single_le_sum (f := fun i => A l i * x i)
            (fun i _ => mul_nonneg (hA l i) (hx0 i)) (Finset.mem_univ j)
        have h2 : ∑ i, A l i * x i ≤ c l / ((k : ℝ) + 1) := by
          have := hAx l; simpa [Matrix.mulVec, dotProduct, hb] using this
        have h3 : c l / ((k : ℝ) + 1) < A l j * (1 / ((k : ℝ) + 1)) := by
          rw [mul_one_div]; exact div_lt_div_of_pos_right hl hk1
        have hxj : x j < 1 / ((k : ℝ) + 1) := lt_of_mul_lt_mul_left (by linarith) hApos.le
        have : r j * x j ≤ r j * (1 / ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left hxj.le (hrj j)
        rw [mul_one_div] at this
        simp only [mul_zero, sub_zero]
        linarith
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hper j
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
    have hHk : Hk (k + 1) = Hk k + 1 / ((k : ℝ) + 1) := by
      simp only [Hk, Finset.sum_range_succ]
    have hdiv : ∑ j, r j / ((k : ℝ) + 1) = (∑ j, r j) * (1 / ((k : ℝ) + 1)) := by
      rw [← Finset.sum_div, mul_one_div]
    have hrx : r ⬝ᵥ x = ∑ j, r j * x j := rfl
    rw [hdiv] at hsum
    rw [hHk, hrx]
    simp only [hWf] at hsum hWlow
    simp only [hD] at hmono
    nlinarith

end FRGapAux

open FRGapAux in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel)
    (T : ℕ) (hT : 1 ≤ T) (C : Fin m → ℝ) (hC : 0 ≤ C) :
    (∑ t ∈ Finset.range T,
        ResolvingNRM.FRUpper.frStateExp A r lam sel T t
          (fun c => r ⬝ᵥ sel (fun l => c l / ((T : ℝ) - t))) C)
      - (∑ j, r j) * (Real.log T + 1) - ∑ j, r j * lam j
      ≤ ResolvingNRM.FRUpper.frValue A r lam sel T C := by
  have h := acc_inv A r lam hlam hr hA sel hsel T C hC
  have hH : Hk T ≤ Real.log T + 1 := by
    have := harmonic_le_one_add_log T
    have e : ((harmonic T : ℚ) : ℝ) = Hk T := by
      simp only [harmonic, Hk]
      push_cast
      refine Finset.sum_congr rfl fun i _ => by rw [one_div]
    rw [e] at this; linarith
  have hr0 : 0 ≤ ∑ j, r j := Finset.sum_nonneg fun j _ => hr j
  have hal : ∑ j, r j * lam j * alive A j C ≤ ∑ j, r j * lam j :=
    Finset.sum_le_sum fun j _ => by
      have := alive_le_one A j C
      have := mul_nonneg (hr j) (hlam j).le
      nlinarith
  have := mul_le_mul_of_nonneg_left hH hr0
  unfold ResolvingNRM.FRUpper.frValue
  unfold Phi at h
  linarith
