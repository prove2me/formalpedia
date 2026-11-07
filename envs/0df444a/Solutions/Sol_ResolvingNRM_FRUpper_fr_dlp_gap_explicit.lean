-- Prove2me | solution 1 for ResolvingNRM.FRUpper.fr_dlp_gap_explicit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:13:43.658445+00:00
-- url     : https://prove2.me/submissions/6d90438a-bedb-4d66-850b-adcff5c7878d

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_FRUpper_Model
import Theorems.Thm_ResolvingNRM_FRUpper_lp_rhs_sensitivity
import Theorems.Thm_ResolvingNRM_FRUpper_fr_revenue_accounting
import Theorems.Thm_ResolvingNRM_FRUpper_lemma8_bound_on_b
import Theorems.Thm_ResolvingNRM_FRUpper_sqrt_sum_bound

open RLPBidPrice.Unbiased Matrix

namespace FRGapAux

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

lemma sel_value (sel : (Fin m → ℝ) → (Fin n → ℝ))
    (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel) (b : Fin m → ℝ) (hb : 0 ≤ b) :
    r ⬝ᵥ sel b = piValue A r b lam := by
  obtain ⟨⟨h1, h2, h3⟩, hopt⟩ := hsel b hb
  unfold piValue
  symm
  apply IsGreatest.csSup_eq
  refine ⟨⟨sel b, h1, h2, h3, rfl⟩, ?_⟩
  rintro v ⟨y, hy1, hy2, hy3, rfl⟩
  exact hopt y hy1 hy2 hy3

lemma le_iSup_fin {n : ℕ} (f : Fin n → ℝ) (j : Fin n) : f j ≤ ⨆ j, f j :=
  le_ciSup (Set.finite_range f).bddAbove j

end FRGapAux

open FRGapAux in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel)
    (T : ℕ) (hT : 1 ≤ T) (C : Fin m → ℝ) (hC : 0 ≤ C) :
    ResolvingNRM.IRT.dlpValue A r lam T C - ResolvingNRM.FRUpper.frValue A r lam sel T C
      ≤ (∑ l, ResolvingNRM.FRUpper.rmaxRes A r l * ResolvingNRM.FRUpper.Kres A lam l) *
          (2 * Real.sqrt T + Real.sqrt 2)
        + n * ResolvingNRM.FRUpper.rMax r * (Real.log T + 1)
        + n * ResolvingNRM.FRUpper.rMax r * ResolvingNRM.FRUpper.lamMax lam := by
  have hrj : ∀ j, 0 ≤ r j := fun j => hr j
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => (hlam j).le
  set Tr : ℝ := (T : ℝ) with hTr
  set b : Fin m → ℝ := fun l => C l / Tr with hbdef
  have hTpos : (0 : ℝ) < Tr := by rw [hTr]; exact_mod_cast hT
  have hb0 : 0 ≤ b := fun l => div_nonneg (hC l) hTpos.le
  set rm : Fin m → ℝ := fun l => ResolvingNRM.FRUpper.rmaxRes A r l with hrm
  have hrm0 : ∀ l, 0 ≤ rm l := by
    intro l
    simp only [hrm, ResolvingNRM.FRUpper.rmaxRes]
    apply Real.iSup_nonneg
    intro j
    split_ifs with h
    · exact div_nonneg (hrj j) h.le
    · exact le_refl _
  set E : ℕ → ((Fin m → ℝ) → ℝ) → ℝ := fun t g =>
    ResolvingNRM.FRUpper.frStateExp A r lam sel T t g C with hEdef
  have hE : ∀ t, IsExp (E t) := fun t => frState_isExp A r lam hlam sel hsel t T C hC
  set g : ℕ → (Fin m → ℝ) → ℝ := fun t c => r ⬝ᵥ sel (fun l => c l / ((T : ℝ) - t)) with hgdef
  set h : ℕ → Fin m → (Fin m → ℝ) → ℝ := fun t l c => max (C l / T - c l / ((T : ℝ) - t)) 0
    with hhdef
  set s : ℕ → ℝ := fun t => Real.sqrt (∑ i ∈ Finset.range t, 1 / ((T : ℝ) - i - 1) ^ 2) with hsdef
  -- step 1: per-period loss
  have step : ∀ t ∈ Finset.range T, piValue A r b lam - E t (g t) ≤
      (∑ l, rm l * ResolvingNRM.FRUpper.Kres A lam l) * s t := by
    intro t ht
    have htT : t < T := Finset.mem_range.mp ht
    have hpos : (0 : ℝ) < (T : ℝ) - t := by
      have : (t : ℝ) < T := by exact_mod_cast htT
      linarith
    have hgb : BddNN (g t) := by
      refine ⟨r ⬝ᵥ lam, fun c hc => ?_⟩
      have hb' : 0 ≤ (fun l => c l / ((T : ℝ) - t)) := fun l => div_nonneg (hc l) hpos.le
      obtain ⟨⟨-, h0, h1⟩, -⟩ := hsel _ hb'
      simp only [hgdef, dotProduct]
      rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hrj j) (h0 j))]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h1 j) (hrj j)
    have hhb : ∀ l, BddNN (h t l) := by
      intro l
      refine ⟨C l / T, fun c hc => ?_⟩
      have h1 : 0 ≤ c l / ((T : ℝ) - t) := div_nonneg (hc l) hpos.le
      have h2 : 0 ≤ C l / (T : ℝ) := div_nonneg (hC l) hTpos.le
      simp only [hhdef]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith) h2
    -- pointwise
    have pw : ∀ c, 0 ≤ c → (1 : ℝ) * piValue A r b lam + (-1) * g t c ≤ ∑ l, rm l * h t l c := by
      intro c hc
      have hb' : 0 ≤ (fun l => c l / ((T : ℝ) - t)) := fun l => div_nonneg (hc l) hpos.le
      have e1 : g t c = piValue A r (fun l => c l / ((T : ℝ) - t)) lam :=
        sel_value A r lam sel hsel _ hb'
      have := ResolvingNRM.FRUpper.lp_rhs_sensitivity A r lam hlam hr hA b _ hb0 hb'
      rw [e1]
      simpa [hrm, hhdef, hbdef] using this
    have hsum := (hE t).sum Finset.univ rm (h t) hhb
    have hm := (hE t).mono (fun c => (1 : ℝ) * piValue A r b lam + (-1) * g t c)
      (fun c => ∑ l, rm l * h t l c) (bddNN_lin (bddNN_const _) hgb 1 (-1)) hsum.1 pw
    rw [(hE t).lin _ _ (bddNN_const _) hgb 1 (-1), (hE t).const, hsum.2] at hm
    have h8 : ∀ l, E t (h t l) ≤ ResolvingNRM.FRUpper.Kres A lam l * s t := fun l =>
      ResolvingNRM.FRUpper.lemma8_bound_on_b A r lam hlam hr hA sel hsel T t htT C hC l
    have : ∑ l, rm l * E t (h t l) ≤ ∑ l, rm l * (ResolvingNRM.FRUpper.Kres A lam l * s t) :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h8 l) (hrm0 l)
    rw [Finset.sum_mul]
    calc piValue A r b lam - E t (g t) = 1 * piValue A r b lam + -1 * E t (g t) := by ring
      _ ≤ _ := hm
      _ ≤ _ := this
      _ = _ := Finset.sum_congr rfl fun l _ => by ring
  -- step 2: sum over periods
  have hK0 : 0 ≤ ∑ l, rm l * ResolvingNRM.FRUpper.Kres A lam l :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hrm0 l) (Real.sqrt_nonneg _)
  have hss := ResolvingNRM.FRUpper.sqrt_sum_bound T hT
  have sum1 : Tr * piValue A r b lam - ∑ t ∈ Finset.range T, E t (g t) ≤
      (∑ l, rm l * ResolvingNRM.FRUpper.Kres A lam l) * (2 * Real.sqrt T + Real.sqrt 2) := by
    have e : Tr * piValue A r b lam - ∑ t ∈ Finset.range T, E t (g t) =
        ∑ t ∈ Finset.range T, (piValue A r b lam - E t (g t)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [e]
    calc _ ≤ ∑ t ∈ Finset.range T, (∑ l, rm l * ResolvingNRM.FRUpper.Kres A lam l) * s t :=
          Finset.sum_le_sum step
      _ = (∑ l, rm l * ResolvingNRM.FRUpper.Kres A lam l) * ∑ t ∈ Finset.range T, s t := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hss hK0
  -- step 3: accounting
  have hacc := ResolvingNRM.FRUpper.fr_revenue_accounting A r lam hlam hr hA sel hsel T hT C hC
  -- step 4: constants
  have hrmax : ∀ j, r j ≤ ResolvingNRM.FRUpper.rMax r := fun j => le_iSup_fin r j
  have hlmax : ∀ j, lam j ≤ ResolvingNRM.FRUpper.lamMax lam := fun j => le_iSup_fin lam j
  have c1 : (∑ j, r j) ≤ n * ResolvingNRM.FRUpper.rMax r := by
    calc (∑ j, r j) ≤ ∑ _j : Fin n, ResolvingNRM.FRUpper.rMax r := Finset.sum_le_sum fun j _ => hrmax j
      _ = _ := by simp
  have c2 : (∑ j, r j * lam j) ≤ n * ResolvingNRM.FRUpper.rMax r * ResolvingNRM.FRUpper.lamMax lam := by
    calc (∑ j, r j * lam j) ≤ ∑ _j : Fin n, ResolvingNRM.FRUpper.rMax r * ResolvingNRM.FRUpper.lamMax lam :=
          Finset.sum_le_sum fun j _ => mul_le_mul (hrmax j) (hlmax j) (hlam0 j) ((hrj j).trans (hrmax j))
      _ = _ := by simp; ring
  have hlog : 0 ≤ Real.log T + 1 := by
    have : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast hT)
    linarith
  have c1' := mul_le_mul_of_nonneg_right c1 hlog
  have hdlp : ResolvingNRM.IRT.dlpValue A r lam T C = Tr * piValue A r b lam := rfl
  rw [hdlp]
  simp only [hEdef, hgdef] at sum1
  simp only [hrm] at sum1
  linarith
