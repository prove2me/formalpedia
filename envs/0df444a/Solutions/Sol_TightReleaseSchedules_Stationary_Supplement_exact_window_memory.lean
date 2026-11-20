-- Prove2me | solution 1 for TightReleaseSchedules.Stationary.Supplement.exact_window_memory
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:34:50.812207+00:00
-- url     : https://prove2.me/submissions/c50f2601-4088-490d-ae6b-99f02b54a14d

import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_window_memory

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary.Supplement

noncomputable section
namespace TRS.Dev.WindowPart1

def lossL {k : ℕ} (W : ℕ) (l : List (StreamRow k)) (ω : Fin k → ℝ) : ℝ :=
  (1 / (2 * (W : ℝ))) * (l.map (fun row => (row.2 - ∑ c, row.1 c * ω c) ^ 2)).sum

def listAlg (k W : ℕ) : StreamAlgorithm k where
  State := List (StreamRow k)
  init := []
  update := fun s row => (row :: s).take W
  query := fun s ω ω' => lossL W s ω - lossL W s ω'

theorem state_eq {k : ℕ} (W : ℕ) (x : ℕ → StreamRow k) (t : ℕ) :
    (listAlg k W).stateAfter x t = ((List.range t).reverse.map x).take W := by
  induction t with
  | zero => simp [StreamAlgorithm.stateAfter, listAlg]
  | succ n ih =>
    have : (listAlg k W).stateAfter x (n + 1) = (x n :: (listAlg k W).stateAfter x n).take W := rfl
    rw [this, ih, List.range_succ, List.reverse_append]
    cases W with
    | zero => exact rfl
    | succ m =>
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
        List.singleton_append, List.take_succ_cons, List.take_take]
      congr 2
      simp

theorem sum_range' (g : ℕ → ℝ) (a n : ℕ) :
    ((List.range' a n).map g).sum = ∑ i ∈ Finset.range n, g (a + i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range'_concat, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem sum_state {k : ℕ} (W : ℕ) (x : ℕ → StreamRow k) (t : ℕ) (f : StreamRow k → ℝ) :
    (((listAlg k W).stateAfter x t).map f).sum = ∑ i ∈ Finset.Ico (t - W) t, f (x i) := by
  rw [state_eq, ← List.map_take, List.map_map]
  rw [List.take_reverse]
  rw [List.map_reverse, List.sum_reverse, List.length_range, List.range_eq_range', List.drop_range']
  rw [Finset.sum_Ico_eq_sum_range, sum_range' (f ∘ x)]
  simp

open Classical in
def Lle {α : Type} (S : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | m + 1 => insert [] ((S ×ˢ Lle S m).image (fun p => p.1 :: p.2))

open Classical in
theorem mem_Lle {α : Type} (S : Finset α) : ∀ (m : ℕ) (l : List α),
    l.length ≤ m → (∀ a ∈ l, a ∈ S) → l ∈ Lle S m
  | 0, l, hl, _ => by
    have : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    subst this; simp [Lle]
  | m + 1, l, hl, hS => by
    cases l with
    | nil => simp [Lle]
    | cons a l =>
      simp only [Lle, Finset.mem_insert, Finset.mem_image, Finset.mem_product, Prod.exists]
      right
      exact ⟨a, l, ⟨hS a (by simp), mem_Lle S m l (by simpa using hl)
        (fun c hc => hS c (by simp [hc]))⟩, rfl⟩

open Classical in
theorem card_Lle {α : Type} (S : Finset α) (N : ℕ) (hN : S.card ≤ N) (hN1 : 1 ≤ N) :
    ∀ m : ℕ, (Lle S m).card ≤ (m + 1) * N ^ m
  | 0 => by simp [Lle]
  | m + 1 => by
    have ih := card_Lle S N hN hN1 m
    simp only [Lle]
    calc (insert [] ((S ×ˢ Lle S m).image (fun p => p.1 :: p.2))).card
        ≤ ((S ×ˢ Lle S m).image (fun p => p.1 :: p.2)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (S ×ˢ Lle S m).card + 1 := by gcongr; exact Finset.card_image_le
      _ = S.card * (Lle S m).card + 1 := by rw [Finset.card_product]
      _ ≤ N * ((m + 1) * N ^ m) + 1 := by gcongr
      _ ≤ (m + 1 + 1) * N ^ (m + 1) := by
        have : 1 ≤ N ^ (m + 1) := Nat.one_le_pow _ _ hN1
        rw [pow_succ] at this ⊢; nlinarith

theorem query_exact {k : ℕ} (W : ℕ) (x : ℕ → StreamRow k) (t : ℕ) (ω ω' : Fin k → ℝ) :
    (listAlg k W).query ((listAlg k W).stateAfter x t) ω ω' = windowGain W x t ω ω' := by
  have h : ∀ v : Fin k → ℝ, lossL W ((listAlg k W).stateAfter x t) v = windowLoss W x t v := by
    intro v
    unfold lossL windowLoss
    rw [sum_state W x t (fun row => (row.2 - ∑ c, row.1 c * v c) ^ 2)]
  unfold windowGain
  show lossL W _ ω - lossL W _ ω' = _
  rw [h ω, h ω']

theorem part1 (W k b : ℕ) (A : Fin (k + 1) → Finset ℝ) (hA : ∀ c, (A c).card ≤ 2 ^ b) :
    ∃ alg : StreamAlgorithm k,
        (∀ x : ℕ → StreamRow k, (∀ n, RowInAlphabet (fun c => (A c : Set ℝ)) (x n)) →
          ∀ t, W ≤ t → ∀ ω ω' : Fin k → ℝ,
            alg.query (alg.stateAfter x t) ω ω' = windowGain W x t ω ω') ∧
        (alg.reachable (RowInAlphabet (fun c => (A c : Set ℝ)))).encard ≤
          (2 ^ (W * (k + 1) * b + Nat.clog 2 W + Nat.clog 2 (W + 1)) : ℕ) := by
  classical
  refine ⟨listAlg k W, fun x _ t _ ω ω' => query_exact W x t ω ω', ?_⟩
  let S : Finset (StreamRow k) :=
    (Fintype.piFinset (fun c : Fin k => A c.castSucc)) ×ˢ A (Fin.last k)
  have hSmem : ∀ row : StreamRow k, RowInAlphabet (fun c => (A c : Set ℝ)) row → row ∈ S := by
    intro row hr
    simp only [S, Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨fun c => by simpa using hr.1 c, by simpa using hr.2⟩
  have hScard : S.card ≤ 2 ^ ((k + 1) * b) := by
    simp only [S, Finset.card_product, Fintype.card_piFinset]
    calc (∏ c : Fin k, (A c.castSucc).card) * (A (Fin.last k)).card
        ≤ (∏ _c : Fin k, 2 ^ b) * 2 ^ b := by
          gcongr with c
          · exact hA _
          · exact hA _
      _ = 2 ^ ((k + 1) * b) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, ← pow_add]
          congr 1; ring
  have hsub : (listAlg k W).reachable (RowInAlphabet (fun c => (A c : Set ℝ))) ⊆
      ((Lle S W : Finset (List (StreamRow k))) : Set (List (StreamRow k))) := by
    rintro σ ⟨x, hx, t, rfl⟩
    apply Finset.mem_coe.mpr
    apply mem_Lle
    · rw [state_eq]; simp
    · intro a ha
      rw [state_eq] at ha
      have := List.mem_of_mem_take ha
      rw [List.mem_map] at this
      obtain ⟨i, _, rfl⟩ := this
      exact hSmem _ (hx i)
  refine (Set.encard_le_encard hsub).trans ?_
  refine le_trans (le_of_eq (Set.encard_coe_eq_coe_finsetCard (Lle S W))) ?_
  have hc := card_Lle S (2 ^ ((k + 1) * b)) hScard (Nat.one_le_two_pow) W
  have h1 : W + 1 ≤ 2 ^ Nat.clog 2 (W + 1) := Nat.le_pow_clog (by norm_num) _
  have h2 : 1 ≤ 2 ^ Nat.clog 2 W := Nat.one_le_two_pow
  have : (Lle S W).card ≤ 2 ^ (W * (k + 1) * b + Nat.clog 2 W + Nat.clog 2 (W + 1)) := by
    calc (Lle S W).card ≤ (W + 1) * (2 ^ ((k + 1) * b)) ^ W := hc
      _ ≤ 2 ^ Nat.clog 2 (W + 1) * (2 ^ ((k + 1) * b)) ^ W := by gcongr
      _ = 2 ^ (W * (k + 1) * b + Nat.clog 2 (W + 1)) := by
          rw [← pow_mul, ← pow_add]
          congr 1; ring
      _ ≤ _ := by gcongr <;> omega
  exact_mod_cast this

abbrev Win (W k b : ℕ) := Fin W → Fin k → Fin (2 ^ b)

def stream {W k b : ℕ} (w : Win W k b) : ℕ → StreamRow k := fun n =>
  if h : n < W then ((fun c => ((w ⟨n, h⟩ c : ℕ) : ℝ)), 0) else (0, 0)

theorem stream_restricted {W k b : ℕ} (w : Win W k b) (n : ℕ) : RestrictedRow b (stream w n) := by
  unfold stream
  split_ifs with h
  · exact ⟨fun c => ⟨(w ⟨n, h⟩ c : ℕ), (w ⟨n, h⟩ c).2, rfl⟩, rfl⟩
  · exact ⟨fun c => ⟨0, by positivity, by simp⟩, rfl⟩

theorem stream_ge {W k b : ℕ} (w : Win W k b) (n : ℕ) (hn : W ≤ n) : stream w n = (0, 0) := by
  unfold stream; simp [Nat.not_lt.mpr hn]

theorem cont_eq {k : ℕ} (alg : StreamAlgorithm k) (x x' : ℕ → StreamRow k) (W : ℕ)
    (hs : alg.stateAfter x W = alg.stateAfter x' W) (hx : ∀ n, W ≤ n → x n = x' n) :
    ∀ t, W ≤ t → alg.stateAfter x t = alg.stateAfter x' t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hs
  | succ n hn ih =>
    show alg.update (alg.stateAfter x n) (x n) = alg.update (alg.stateAfter x' n) (x' n)
    rw [ih, hx n hn]

theorem gain_formula {k : ℕ} (W : ℕ) (x : ℕ → StreamRow k) (hx : ∀ n, (x n).2 = 0) (t : ℕ)
    (j : Fin k) :
    windowGain W x t 0 (coordVec j) =
      -((1 / (2 * (W : ℝ))) * ∑ i ∈ Finset.Ico (t - W) t, ((x i).1 j) ^ 2) := by
  unfold windowGain windowLoss
  have h1 : ∀ i, ((x i).2 - ∑ c, (x i).1 c * (0 : Fin k → ℝ) c) ^ 2 = 0 := by
    intro i; simp [hx i]
  have h2 : ∀ i, ((x i).2 - ∑ c, (x i).1 c * coordVec j c) ^ 2 = ((x i).1 j) ^ 2 := by
    intro i
    simp [hx i, coordVec, Pi.single_apply]
  simp only [h1, h2, Finset.sum_const_zero, mul_zero, zero_sub]

theorem part2 (W k b : ℕ) (alg : StreamAlgorithm k)
    (h : ∀ x : ℕ → StreamRow k, (∀ n, RestrictedRow b (x n)) →
        ∀ t, W ≤ t → ∀ j : Fin k,
          alg.query (alg.stateAfter x t) 0 (coordVec j) = windowGain W x t 0 (coordVec j)) :
    ((2 ^ (W * k * b) : ℕ) : ℕ∞) ≤ (alg.reachable (RestrictedRow b)).encard := by
  classical
  let f : Win W k b → alg.State := fun w => alg.stateAfter (stream w) W
  have hinj : Function.Injective f := by
    intro w w' hww
    by_contra hne
    have hD : (Finset.univ.filter (fun q : Fin W => ∃ j, w q j ≠ w' q j)).Nonempty := by
      by_contra hE
      apply hne
      funext q j
      by_contra hqj
      exact hE ⟨q, by simpa using ⟨j, hqj⟩⟩
    set q := (Finset.univ.filter (fun q : Fin W => ∃ j, w q j ≠ w' q j)).max' hD with hq
    have hqmem := Finset.max'_mem _ hD
    rw [← hq, Finset.mem_filter] at hqmem
    obtain ⟨j, hj⟩ := hqmem.2
    have hlater : ∀ i : Fin W, q < i → ∀ c, w i c = w' i c := by
      intro i hi c
      by_contra hc
      have : i ∈ Finset.univ.filter (fun q : Fin W => ∃ j, w q j ≠ w' q j) := by
        simpa using ⟨c, hc⟩
      exact absurd (Finset.le_max' _ i this) (not_le.mpr hi)
    have hst := cont_eq alg (stream w) (stream w') W hww
      (fun n hn => by rw [stream_ge w n hn, stream_ge w' n hn]) (W + q) (by omega)
    have e1 := h (stream w) (stream_restricted w) (W + q) (by omega) j
    have e2 := h (stream w') (stream_restricted w') (W + q) (by omega) j
    rw [hst] at e1
    have hg : windowGain W (stream w) (W + q) 0 (coordVec j) =
        windowGain W (stream w') (W + q) 0 (coordVec j) := by rw [← e1, ← e2]
    have hr : ∀ v : Win W k b, ∀ n, (stream v n).2 = 0 := by
      intro v n; unfold stream; split_ifs <;> rfl
    rw [gain_formula W _ (hr w), gain_formula W _ (hr w')] at hg
    have hWpos : 0 < W := Fin.pos q
    have hc : (1 / (2 * (W : ℝ))) ≠ 0 := by positivity
    have hs := mul_left_cancel₀ hc (neg_injective hg)
    have hqW : W + q - W = q := by omega
    rw [hqW] at hs
    have hqin : (q : ℕ) ∈ Finset.Ico (q : ℕ) (W + q) := by
      simp only [Finset.mem_Ico]; omega
    rw [← Finset.add_sum_erase _ _ hqin, ← Finset.add_sum_erase _ _ hqin] at hs
    have hrest : ∑ i ∈ (Finset.Ico (q : ℕ) (W + q)).erase q, ((stream w i).1 j) ^ 2 =
        ∑ i ∈ (Finset.Ico (q : ℕ) (W + q)).erase q, ((stream w' i).1 j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_erase, Finset.mem_Ico] at hi
      by_cases hiW : i < W
      · have := hlater ⟨i, hiW⟩ (by rw [Fin.lt_def]; simp; omega) j
        simp [stream, hiW, this]
      · rw [stream_ge w i (by omega), stream_ge w' i (by omega)]
    have hq1 : (((w q j : ℕ) : ℝ)) ^ 2 = (((w' q j : ℕ) : ℝ)) ^ 2 := by
      have := add_right_cancel (hs.trans (by rw [hrest]) : _ + _ = _ + _)
      simpa [stream] using this
    have hq2 : (w q j : ℕ) = (w' q j : ℕ) := by
      have h0 : (0 : ℝ) ≤ ((w q j : ℕ) : ℝ) := Nat.cast_nonneg _
      have h0' : (0 : ℝ) ≤ ((w' q j : ℕ) : ℝ) := Nat.cast_nonneg _
      exact_mod_cast (pow_left_inj₀ h0 h0' two_ne_zero).mp hq1
    exact hj (Fin.ext hq2)
  have hsub : Set.range f ⊆ alg.reachable (RestrictedRow b) := by
    rintro _ ⟨w, rfl⟩
    exact ⟨stream w, stream_restricted w, W, rfl⟩
  refine le_trans ?_ (Set.encard_le_encard hsub)
  refine le_trans ?_ hinj.encard_range
  rw [ENat.card_eq_coe_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_fin]
  apply le_of_eq
  norm_cast
  rw [← pow_mul, ← pow_mul]
  congr 1
  ring

theorem part4 (W k b : ℕ) (hk : 0 < k) (hb : 0 < b) :
    W * (k + 1) * b + Nat.clog 2 W + Nat.clog 2 (W + 1) ≤ 4 * (W * k * b) := by
  have h1 : Nat.clog 2 W ≤ W := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact (Nat.lt_two_pow_self).le
  have h2 : Nat.clog 2 (W + 1) ≤ W := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact Nat.lt_two_pow_self
  have h3 : W ≤ W * k * b := by
    calc W = W * 1 * 1 := by ring
      _ ≤ W * k * b := by gcongr <;> omega
  have h4 : W * (k + 1) * b = W * k * b + W * b := by ring
  have h5 : W * b ≤ W * k * b := by
    calc W * b = W * 1 * b := by ring
      _ ≤ W * k * b := by gcongr; omega
  omega

end TRS.Dev.WindowPart1
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary.Supplement

/-
PLAN for part (3).  E = W*k entries (q,j), N = 2^b values each, windows w : Fin W -> Fin k -> Fin N.
Stream x_w: rows (w q ., 0) for n < W, zero rows after.  Query at t = W+q, (0, e_j): the exact answer
is -(1/2W) * sum_{i in [q,W)} w_{ij}^2, which together with the later entries w_{ij}, i > q, determines w_{qj}.
(a) Measure part: with law = P x (Q^N x Q), the sets {rho | answer(rho,w,e) = G(w,e)} are measurable of
    measure >= 2/3; summing over (w,e) and a mean-value argument gives ONE fixed rho for which
    3 * #{(w,e) correct} >= 2 * E * N^E.  For this fixed rho the algorithm is deterministic:
    the answer at (w,e) is a function a_e(sigma(w)) of the M-bit state sigma(w) = state after W rows.
(b) Counting: guess_e(w) := min(sqrt(floor(-2W a_e(sigma w) - sum_{i>q} w_ij^2)), N-1).  If the answer is
    correct then guess = w_e.  Code c_e(w) = none if w_e = guess_e(w), else some(rank of w_e among the N-1
    other values).  On a fibre sigma = const, w -> c(w) is injective (downward induction on q), so
    sum_{w in fibre} N^{#S(w)} <= (N + N-1)^E, hence  sum_w N^{#S(w)} <= 2^M (2N-1)^E.
(c) Tangent-line Jensen with exp:  sum_w N^{cw} >= N^E * N^{(2/3)E}.  So N^{5E} <= 2^{3M}(2N-1)^{3E}
    which contradicts 2^{64M} < N^E (since N^317 >= (2N-1)^192 for N >= 2).  Hence 64M >= E b, and the
    claim follows since 1 - h2(1/10) <= 1.
-/

set_option exponentiation.threshold 1000
noncomputable section
namespace TRS.Dev.WindowPart3

abbrev Win (W k N : ℕ) := Fin W → Fin k → Fin N

def rankC {N : ℕ} (g v : Fin N) : ℕ := if v.val < g.val then v.val else v.val - 1

theorem rankC_lt {N : ℕ} (g v : Fin N) (h : v ≠ g) : rankC g v < N - 1 := by
  unfold rankC
  have hv := v.2
  have hg := g.2
  have : v.val ≠ g.val := fun e => h (Fin.ext e)
  split_ifs <;> omega

theorem rankC_inj {N : ℕ} (g v v' : Fin N) (h : v ≠ g) (h' : v' ≠ g)
    (e : rankC g v = rankC g v') : v = v' := by
  unfold rankC at e
  have : v.val ≠ g.val := fun e => h (Fin.ext e)
  have : v'.val ≠ g.val := fun e => h' (Fin.ext e)
  apply Fin.ext
  split_ifs at e <;> omega

def codeW {W k N : ℕ} (guess : Fin W × Fin k → Win W k N → Fin N) (w : Win W k N) :
    Fin W × Fin k → Option ℕ := fun e =>
  if w e.1 e.2 = guess e w then none else some (rankC (guess e w) (w e.1 e.2))

theorem code_inj {W k N : ℕ} {Q : Type} (σ : Win W k N → Q)
    (guess : Fin W × Fin k → Win W k N → Fin N)
    (hdep : ∀ w w' (q : Fin W) (j : Fin k), σ w = σ w' →
      (∀ i : Fin W, q < i → ∀ c, w i c = w' i c) → guess (q, j) w = guess (q, j) w')
    (w w' : Win W k N) (hσ : σ w = σ w') (hc : codeW guess w = codeW guess w') : w = w' := by
  have key : ∀ m : ℕ, ∀ q : Fin W, W - q.val ≤ m → ∀ j, w q j = w' q j := by
    intro m
    induction m with
    | zero => intro q hq; exact absurd hq (by have := q.2; omega)
    | succ m ih =>
      intro q hq j
      have hlater : ∀ i : Fin W, q < i → ∀ c, w i c = w' i c := by
        intro i hi c
        exact ih i (by rw [Fin.lt_def] at hi; omega) c
      have hg := hdep w w' q j hσ hlater
      have hce := congrFun hc (q, j)
      unfold codeW at hce
      simp only at hce
      rw [← hg] at hce
      by_cases h1 : w q j = guess (q, j) w
      · by_cases h2 : w' q j = guess (q, j) w
        · rw [h1, h2]
        · rw [if_pos h1, if_neg h2] at hce; exact absurd hce (by simp)
      · by_cases h2 : w' q j = guess (q, j) w
        · rw [if_neg h1, if_pos h2] at hce; exact absurd hce (by simp)
        · rw [if_neg h1, if_neg h2] at hce
          exact rankC_inj _ _ _ h1 h2 (Option.some.inj hce)
  funext q j
  exact key W q (by omega) j

open Classical in
theorem comb_sum {W k N : ℕ} (hN : 1 ≤ N) {Q : Type} [Fintype Q] (σ : Win W k N → Q)
    (guess : Fin W × Fin k → Win W k N → Fin N)
    (hdep : ∀ w w' (q : Fin W) (j : Fin k), σ w = σ w' →
      (∀ i : Fin W, q < i → ∀ c, w i c = w' i c) → guess (q, j) w = guess (q, j) w') :
    ∑ w : Win W k N, N ^ (Finset.univ.filter (fun e : Fin W × Fin k =>
        w e.1 e.2 = guess e w)).card ≤ Fintype.card Q * (2 * N - 1) ^ (W * k) := by
  rw [← Finset.sum_fiberwise Finset.univ σ]
  refine (Finset.sum_le_card_nsmul _ _ ((2 * N - 1) ^ (W * k)) ?_).trans ?_
  · intro q0 _
    let wt : Option ℕ → ℕ := fun o => o.elim N (fun _ => 1)
    let T : Finset (Option ℕ) := insert none ((Finset.range (N - 1)).image some)
    have hf : ∀ w : Win W k N, N ^ (Finset.univ.filter (fun e : Fin W × Fin k =>
        w e.1 e.2 = guess e w)).card = ∏ e, wt (codeW guess w e) := by
      intro w
      have : ∀ e, wt (codeW guess w e) = if w e.1 e.2 = guess e w then N else 1 := by
        intro e; unfold codeW; split_ifs <;> simp [wt]
      simp only [this, Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
    simp only [hf]
    rw [← Finset.sum_image (f := fun c : Fin W × Fin k → Option ℕ => ∏ e, wt (c e))
      (s := Finset.univ.filter (fun w => σ w = q0)) (g := codeW guess)
      (fun w hw w' hw' h => code_inj σ guess hdep w w'
        ((Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hw').2.symm) h)]
    have hsub : (Finset.univ.filter (fun w => σ w = q0)).image (codeW guess) ⊆
        Fintype.piFinset (fun _ : Fin W × Fin k => T) := by
      intro c hc
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hc
      rw [Fintype.mem_piFinset]
      intro e
      simp only [T, codeW]
      split_ifs with h
      · simp
      · simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
        exact Or.inr ⟨_, rankC_lt _ _ h, rfl⟩
    refine (Finset.sum_le_sum_of_subset hsub).trans ?_
    rw [← Finset.prod_univ_sum (fun _ : Fin W × Fin k => T) (fun _ o => wt o)]
    have : ∑ o ∈ T, wt o = 2 * N - 1 := by
      simp only [T]
      rw [Finset.sum_insert (by simp), Finset.sum_image (by simp)]
      simp [wt]
      omega
    simp [this]
  · simp [mul_comm]

theorem jensen_exp {α : Type} [Fintype α] [Nonempty α] (c : α → ℕ) (N E : ℕ) (hN : 2 ≤ N)
    (hc : 2 * E * Fintype.card α ≤ 3 * ∑ w, c w) :
    ((Fintype.card α : ℝ) ^ 3) * (N : ℝ) ^ (2 * E) ≤ (∑ w, (N : ℝ) ^ (c w)) ^ 3 := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  set L := Real.log N with hL
  have hLpos : 0 < L := Real.log_pos (by exact_mod_cast hN)
  have hpow : ∀ m : ℕ, (N : ℝ) ^ m = Real.exp (m * L) := by
    intro m
    rw [hL, Real.exp_nat_mul, Real.exp_log hNpos]
  set u : ℝ := (∑ w, (c w : ℝ)) / Fintype.card α with hu
  have hsum : ∑ w, ((c w : ℝ) - u) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hu]
    field_simp
    simp
  have h1 : ∀ w, Real.exp (u * L) * (1 + ((c w : ℝ) - u) * L) ≤ (N : ℝ) ^ (c w) := by
    intro w
    rw [hpow]
    have := Real.add_one_le_exp (((c w : ℝ) - u) * L)
    have h2 : Real.exp ((c w : ℝ) * L) = Real.exp (u * L) * Real.exp (((c w : ℝ) - u) * L) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    linarith
  have h3 : Fintype.card α * Real.exp (u * L) ≤ ∑ w, (N : ℝ) ^ (c w) := by
    refine le_trans ?_ (Finset.sum_le_sum (fun w _ => h1 w))
    rw [← Finset.mul_sum]
    have : ∑ w, (1 + ((c w : ℝ) - u) * L) = Fintype.card α := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum]; simp
    rw [this]; rw [mul_comm]
  have hu2 : (2 * E : ℝ) / 3 ≤ u := by
    rw [hu, le_div_iff₀ hn]
    have : (2 * E * Fintype.card α : ℝ) ≤ 3 * ∑ w, (c w : ℝ) := by exact_mod_cast hc
    linarith
  have h4 : Real.exp ((2 * E : ℝ) / 3 * L) ≤ Real.exp (u * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hu2 hLpos.le)
  have h5 : ((Fintype.card α : ℝ) * Real.exp ((2 * E : ℝ) / 3 * L)) ^ 3 ≤
      (∑ w, (N : ℝ) ^ (c w)) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    refine le_trans ?_ h3
    exact mul_le_mul_of_nonneg_left h4 hn.le
  refine le_trans (le_of_eq ?_) h5
  rw [mul_pow, ← Real.exp_nat_mul, hpow]
  congr 2
  push_cast; ring

theorem final_arith (b E M : ℕ) (hb : 1 ≤ b) (hE : 1 ≤ E)
    (h : (2 ^ b) ^ (5 * E) ≤ 2 ^ (3 * M) * (2 * 2 ^ b - 1) ^ (3 * E)) : E * b ≤ 64 * M := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨N, hNdef⟩ : ∃ N, N = 2 ^ b := ⟨_, rfl⟩
  rw [← hNdef] at h
  have hN2 : 2 ≤ N := by
    rw [hNdef]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hlt' : 2 ^ (64 * M) < N ^ E := by
    rw [hNdef, ← pow_mul]
    apply Nat.pow_lt_pow_right (by norm_num); linarith [mul_comm E b]
  have h1 : (N ^ (5 * E)) ^ 64 ≤ (2 ^ (3 * M) * (2 * N - 1) ^ (3 * E)) ^ 64 :=
    Nat.pow_le_pow_left h 64
  have h2 : (2 ^ (3 * M) * (2 * N - 1) ^ (3 * E)) ^ 64 =
      (2 ^ (64 * M)) ^ 3 * ((2 * N - 1) ^ 192) ^ E := by
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
      show 3 * M * 64 = 64 * M * 3 by ring, show 3 * E * 64 = 192 * E by ring]
  have h3 : (N ^ (5 * E)) ^ 64 = (N ^ 320) ^ E := by
    rw [← pow_mul, ← pow_mul, show 5 * E * 64 = 320 * E by ring]
  have hpos : 0 < ((2 * N - 1) ^ 192) ^ E := by
    apply pow_pos; apply pow_pos; omega
  have h4 : (2 ^ (64 * M)) ^ 3 < (N ^ E) ^ 3 := Nat.pow_lt_pow_left hlt' (by norm_num)
  have h5 : (N ^ 320) ^ E < (N ^ 3) ^ E * ((2 * N - 1) ^ 192) ^ E := by
    calc (N ^ 320) ^ E ≤ (2 ^ (64 * M)) ^ 3 * ((2 * N - 1) ^ 192) ^ E := by
          rw [← h3, ← h2]; exact h1
      _ < (N ^ E) ^ 3 * ((2 * N - 1) ^ 192) ^ E := by
          exact Nat.mul_lt_mul_of_pos_right h4 hpos
      _ = (N ^ 3) ^ E * ((2 * N - 1) ^ 192) ^ E := by
          rw [show (N ^ E) ^ 3 = (N ^ 3) ^ E by rw [← pow_mul, ← pow_mul, mul_comm]]
  have h6 : (N ^ 317) ^ E < ((2 * N - 1) ^ 192) ^ E := by
    have : (N ^ 320) ^ E = (N ^ 317) ^ E * (N ^ 3) ^ E := by
      rw [← mul_pow, ← pow_add]
    rw [this] at h5
    have hNp : 0 < (N ^ 3) ^ E := by positivity
    nlinarith
  have h7 : N ^ 317 < (2 * N - 1) ^ 192 := lt_of_pow_lt_pow_left₀ E (by positivity) h6
  have hmain : (2 * N - 1) ^ 192 ≤ N ^ 317 := by
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · have : b = 1 := by omega
      have hN : N = 2 := by rw [hNdef, this]; norm_num
      rw [hN]; norm_num
    · have hN4 : 4 ≤ N := by
        rw [hNdef]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb2
      have e1 : (2 * N - 1) ^ 192 ≤ (2 * N) ^ 192 := Nat.pow_le_pow_left (by omega) 192
      have e2 : 2 ^ 192 ≤ N ^ 125 := by
        calc 2 ^ 192 ≤ 4 ^ 125 := by norm_num
          _ ≤ N ^ 125 := Nat.pow_le_pow_left hN4 125
      calc (2 * N - 1) ^ 192 ≤ (2 * N) ^ 192 := e1
        _ = 2 ^ 192 * N ^ 192 := by rw [mul_pow]
        _ ≤ N ^ 125 * N ^ 192 := Nat.mul_le_mul_right _ e2
        _ = N ^ 317 := by rw [← pow_add]
  exact absurd h7 (not_lt.mpr hmain)

def stream {W k b : ℕ} (w : Win W k (2 ^ b)) : ℕ → StreamRow k := fun n =>
  if h : n < W then ((fun c => ((w ⟨n, h⟩ c : ℕ) : ℝ)), 0) else (0, 0)

theorem stream_restricted {W k b : ℕ} (w : Win W k (2 ^ b)) (n : ℕ) :
    RestrictedRow b (stream w n) := by
  unfold stream
  split_ifs with h
  · exact ⟨fun c => ⟨(w ⟨n, h⟩ c : ℕ), (w ⟨n, h⟩ c).2, rfl⟩, rfl⟩
  · exact ⟨fun c => ⟨0, by positivity, by simp⟩, rfl⟩

theorem stream_ge {W k b : ℕ} (w : Win W k (2 ^ b)) (n : ℕ) (hn : W ≤ n) :
    stream w n = (0, 0) := by
  unfold stream; simp [Nat.not_lt.mpr hn]

theorem stream_snd {W k b : ℕ} (w : Win W k (2 ^ b)) (n : ℕ) : (stream w n).2 = 0 := by
  unfold stream; split_ifs <;> rfl

theorem stream_lt {W k b : ℕ} (w : Win W k (2 ^ b)) (i : ℕ) (hi : i < W) (j : Fin k) :
    (stream w i).1 j = ((w ⟨i, hi⟩ j : ℕ) : ℝ) := by
  unfold stream; simp [hi]

theorem gain_formula {k : ℕ} (W : ℕ) (x : ℕ → StreamRow k) (hx : ∀ n, (x n).2 = 0) (t : ℕ)
    (j : Fin k) :
    windowGain W x t 0 (coordVec j) =
      -((1 / (2 * (W : ℝ))) * ∑ i ∈ Finset.Ico (t - W) t, ((x i).1 j) ^ 2) := by
  unfold windowGain windowLoss
  have h1 : ∀ i, ((x i).2 - ∑ c, (x i).1 c * (0 : Fin k → ℝ) c) ^ 2 = 0 := by
    intro i; simp [hx i]
  have h2 : ∀ i, ((x i).2 - ∑ c, (x i).1 c * coordVec j c) ^ 2 = ((x i).1 j) ^ 2 := by
    intro i
    simp [hx i, coordVec, Pi.single_apply]
  simp only [h1, h2, Finset.sum_const_zero, mul_zero, zero_sub]

/-- the true gain of window `w` for entry `(q, j)`: sum of squares of column `j` from row `q` on. -/
theorem gain_eq {W k b : ℕ} (hW : 0 < W) (w : Win W k (2 ^ b)) (q : Fin W) (j : Fin k) :
    -(2 * (W : ℝ)) * windowGain W (stream w) (W + q) 0 (coordVec j) =
      ((w q j : ℕ) : ℝ) ^ 2 +
        ∑ i ∈ Finset.Ico ((q : ℕ) + 1) W, ((stream w i).1 j) ^ 2 := by
  rw [gain_formula W _ (stream_snd w)]
  have hWR : (2 * (W : ℝ)) ≠ 0 := by positivity
  have hqW : W + (q : ℕ) - W = q := by omega
  rw [hqW]
  have hsub : ∑ i ∈ Finset.Ico (q : ℕ) (W + q), ((stream w i).1 j) ^ 2 =
      ∑ i ∈ Finset.Ico (q : ℕ) W, ((stream w i).1 j) ^ 2 := by
    symm
    apply Finset.sum_subset
    · intro i; simp only [Finset.mem_Ico]; omega
    · intro i hi hi'
      simp only [Finset.mem_Ico] at hi hi'
      rw [stream_ge w i (by omega)]; simp
  rw [hsub, Finset.sum_eq_sum_Ico_succ_bot q.2, stream_lt w q q.2 j]
  field_simp

open Classical in
def guessD {W k b M : ℕ} (σ : Win W k (2 ^ b) → (Fin M → Bool))
    (a : Fin W × Fin k → (Fin M → Bool) → ℝ) (e : Fin W × Fin k) (w : Win W k (2 ^ b)) :
    Fin (2 ^ b) :=
  ⟨min (Nat.sqrt ⌊-(2 * (W : ℝ)) * a e (σ w) -
      ∑ i ∈ Finset.Ico ((e.1 : ℕ) + 1) W, ((stream w i).1 e.2) ^ 2⌋₊) (2 ^ b - 1),
    by have : 0 < 2 ^ b := by positivity
       omega⟩

theorem guessD_dep {W k b M : ℕ} (σ : Win W k (2 ^ b) → (Fin M → Bool))
    (a : Fin W × Fin k → (Fin M → Bool) → ℝ) (w w' : Win W k (2 ^ b)) (q : Fin W) (j : Fin k)
    (hσ : σ w = σ w') (hl : ∀ i : Fin W, q < i → ∀ c, w i c = w' i c) :
    guessD σ a (q, j) w = guessD σ a (q, j) w' := by
  unfold guessD
  apply Fin.ext
  simp only
  rw [hσ]
  have : ∑ i ∈ Finset.Ico ((q : ℕ) + 1) W, ((stream w i).1 j) ^ 2 =
      ∑ i ∈ Finset.Ico ((q : ℕ) + 1) W, ((stream w' i).1 j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [stream_lt w i (by omega), stream_lt w' i (by omega), hl ⟨i, by omega⟩
      (by rw [Fin.lt_def]; simp; omega) j]
  rw [this]

theorem guessD_correct {W k b M : ℕ} (hW : 0 < W) (σ : Win W k (2 ^ b) → (Fin M → Bool))
    (a : Fin W × Fin k → (Fin M → Bool) → ℝ) (w : Win W k (2 ^ b)) (e : Fin W × Fin k)
    (h : a e (σ w) = windowGain W (stream w) (W + e.1) 0 (coordVec e.2)) :
    w e.1 e.2 = guessD σ a e w := by
  apply Fin.ext
  unfold guessD
  simp only
  have h1 := gain_eq hW w e.1 e.2
  rw [← h] at h1
  have h2 : -(2 * (W : ℝ)) * a e (σ w) - ∑ i ∈ Finset.Ico ((e.1 : ℕ) + 1) W,
      ((stream w i).1 e.2) ^ 2 = (((w e.1 e.2 : ℕ) ^ 2 : ℕ) : ℝ) := by
    push_cast; linarith
  rw [h2, Nat.floor_natCast, Nat.sqrt_eq']
  have := (w e.1 e.2).2
  omega

open Classical in
theorem det_main (W k b M : ℕ) (hW : 0 < W) (hk : 0 < k) (hb : 0 < b)
    (σ : Win W k (2 ^ b) → (Fin M → Bool))
    (a : Fin W × Fin k → (Fin M → Bool) → ℝ)
    (hcount : 2 * (W * k) * (2 ^ b) ^ (W * k) ≤ 3 * ∑ w : Win W k (2 ^ b),
      (Finset.univ.filter (fun e : Fin W × Fin k =>
        a e (σ w) = windowGain W (stream w) (W + e.1) 0 (coordVec e.2))).card) :
    W * k * b ≤ 64 * M := by
  have hN1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hcomb := comb_sum (W := W) (k := k) (N := 2 ^ b) hN1 σ (guessD σ a)
    (fun w w' q j hs hl => guessD_dep σ a w w' q j hs hl)
  have hcard : Fintype.card (Win W k (2 ^ b)) = (2 ^ b) ^ (W * k) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    ring
  have hQ : Fintype.card (Fin M → Bool) = 2 ^ M := by simp
  have : Nonempty (Win W k (2 ^ b)) := ⟨fun _ _ => ⟨0, by positivity⟩⟩
  have hle : ∀ w : Win W k (2 ^ b),
      (2 ^ b) ^ (Finset.univ.filter (fun e : Fin W × Fin k =>
        a e (σ w) = windowGain W (stream w) (W + e.1) 0 (coordVec e.2))).card ≤
      (2 ^ b) ^ (Finset.univ.filter (fun e : Fin W × Fin k =>
        w e.1 e.2 = guessD σ a e w)).card := by
    intro w
    apply Nat.pow_le_pow_right (by positivity)
    apply Finset.card_le_card
    intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.1, guessD_correct hW σ a w e he.2⟩
  have hsum : ∑ w : Win W k (2 ^ b), (2 ^ b) ^ (Finset.univ.filter (fun e : Fin W × Fin k =>
        a e (σ w) = windowGain W (stream w) (W + e.1) 0 (coordVec e.2))).card ≤
      2 ^ M * (2 * 2 ^ b - 1) ^ (W * k) := by
    rw [hQ] at hcomb
    exact (Finset.sum_le_sum (fun w _ => hle w)).trans hcomb
  have hj := jensen_exp (fun w : Win W k (2 ^ b) => (Finset.univ.filter
      (fun e : Fin W × Fin k =>
        a e (σ w) = windowGain W (stream w) (W + e.1) 0 (coordVec e.2))).card)
    (2 ^ b) (W * k) (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb) (by rw [hcard]; exact hcount)
  rw [hcard] at hj
  have hsumR : (∑ w : Win W k (2 ^ b), ((2 ^ b : ℕ) : ℝ) ^ (Finset.univ.filter
      (fun e : Fin W × Fin k =>
        a e (σ w) = windowGain W (stream w) (W + e.1) 0 (coordVec e.2))).card) ≤
      ((2 ^ M * (2 * 2 ^ b - 1) ^ (W * k) : ℕ) : ℝ) := by exact_mod_cast hsum
  have hj2 := hj.trans (pow_le_pow_left₀ (by positivity) hsumR 3)
  have hnat : (2 ^ b) ^ (5 * (W * k)) ≤ 2 ^ (3 * M) * (2 * 2 ^ b - 1) ^ (3 * (W * k)) := by
    have : (((2 ^ b) ^ (5 * (W * k)) : ℕ) : ℝ) ≤
        (((2 ^ (3 * M) * (2 * 2 ^ b - 1) ^ (3 * (W * k))) : ℕ) : ℝ) := by
      have e1 : ((((2 ^ b) ^ (W * k) : ℕ) : ℝ) ^ 3) * (((2 ^ b : ℕ) : ℝ)) ^ (2 * (W * k)) =
          (((2 ^ b) ^ (5 * (W * k)) : ℕ) : ℝ) := by
        push_cast
        ring
      have e2 : (((2 ^ M * (2 * 2 ^ b - 1) ^ (W * k) : ℕ) : ℝ)) ^ 3 =
          (((2 ^ (3 * M) * (2 * 2 ^ b - 1) ^ (3 * (W * k))) : ℕ) : ℝ) := by
        rw [← Nat.cast_pow]
        congr 1
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm M 3, mul_comm (W * k) 3]
      rw [← e1, ← e2]; exact hj2
    exact_mod_cast this
  have := final_arith b (W * k) M hb (Nat.mul_pos hW hk) hnat
  linarith [mul_comm (W * k) b]

section prob

variable {k M : ℕ} (alg : RandomizedStreamAlgorithm k M)

abbrev Omega := alg.Public × ((ℕ → alg.Private) × alg.Private)

theorem meas_state (x : ℕ → StreamRow k) :
    ∀ n : ℕ, Measurable (fun ρ : Omega alg => alg.stateAfter ρ.1 ρ.2.1 x n)
  | 0 => by
    show Measurable (fun ρ : Omega alg => alg.init ρ.1 (ρ.2.1 0))
    exact alg.measurable_init.comp
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)))
  | n + 1 => by
    have ih := meas_state x n
    show Measurable (fun ρ : Omega alg =>
      alg.update ρ.1 (ρ.2.1 (n + 1)) (alg.stateAfter ρ.1 ρ.2.1 x n) (x n))
    have hF : Measurable (fun p : (Fin M → Bool) × Omega alg =>
        alg.update p.2.1 (p.2.2.1 (n + 1)) p.1 (x n)) := by
      apply measurable_from_prod_countable_right
      intro σ
      exact (alg.measurable_update σ (x n)).comp
        (measurable_fst.prodMk ((measurable_pi_apply (n + 1)).comp
          (measurable_fst.comp measurable_snd)))
    exact hF.comp (ih.prodMk measurable_id)

theorem meas_event (x : ℕ → StreamRow k) (t : ℕ) (ω ω' : Fin k → ℝ) (g : ℝ) :
    MeasurableSet {ρ : Omega alg | alg.query ρ.1 ρ.2.2 (alg.stateAfter ρ.1 ρ.2.1 x t) ω ω' = g} := by
  have hF : Measurable (fun p : (Fin M → Bool) × Omega alg =>
      alg.query p.2.1 p.2.2.2 p.1 ω ω') := by
    apply measurable_from_prod_countable_right
    intro σ
    exact (alg.measurable_query σ ω ω').comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have := hF.comp ((meas_state alg x t).prodMk measurable_id)
  exact this (measurableSet_singleton g)

open Classical in
theorem exists_good_rho (W b : ℕ) (hW : 0 < W)
    (h : ∀ x : ℕ → StreamRow k, (∀ n, RestrictedRow b (x n)) →
        ∀ t, W ≤ t → ∀ j : Fin k,
          (2 / 3 : ℝ≥0∞) ≤ alg.probAnswer x t 0 (coordVec j) (windowGain W x t 0 (coordVec j))) :
    ∃ ρ : Omega alg, 2 * (W * k) * (2 ^ b) ^ (W * k) ≤ 3 * ∑ w : Win W k (2 ^ b),
      (Finset.univ.filter (fun e : Fin W × Fin k =>
        alg.query ρ.1 ρ.2.2 (alg.stateAfter ρ.1 ρ.2.1 (stream w) (W + e.1)) 0 (coordVec e.2) =
          windowGain W (stream w) (W + e.1) 0 (coordVec e.2))).card := by
  have hprob : IsProbabilityMeasure alg.law := by
    unfold RandomizedStreamAlgorithm.law; infer_instance
  let A : Win W k (2 ^ b) × (Fin W × Fin k) → Set (Omega alg) := fun i =>
    {ρ | alg.query ρ.1 ρ.2.2 (alg.stateAfter ρ.1 ρ.2.1 (stream i.1) (W + i.2.1)) 0
        (coordVec i.2.2) = windowGain W (stream i.1) (W + i.2.1) 0 (coordVec i.2.2)}
  have hA : ∀ i, MeasurableSet (A i) := fun i => meas_event alg _ _ _ _ _
  have hAp : ∀ i, (2 / 3 : ℝ≥0∞) ≤ alg.law (A i) := fun i =>
    h (stream i.1) (stream_restricted i.1) (W + i.2.1) (by omega) i.2.2
  let f : Omega alg → ℝ≥0∞ := fun ρ => ∑ i, (A i).indicator 1 ρ
  have hint : ∫⁻ ρ, f ρ ∂alg.law = ∑ i, alg.law (A i) := by
    simp only [f]
    rw [lintegral_finsetSum _ (fun i _ => (measurable_one.indicator (hA i)))]
    exact Finset.sum_congr rfl (fun i _ => lintegral_indicator_one (hA i))
  have hfin : ∫⁻ ρ, f ρ ∂alg.law ≠ ⊤ := by
    rw [hint]
    exact ENNReal.sum_ne_top.mpr (fun i _ => measure_ne_top _ _)
  obtain ⟨ρ, hρ⟩ := exists_lintegral_le hfin
  refine ⟨ρ, ?_⟩
  have hfρ : f ρ = ((∑ w : Win W k (2 ^ b),
      (Finset.univ.filter (fun e : Fin W × Fin k =>
        alg.query ρ.1 ρ.2.2 (alg.stateAfter ρ.1 ρ.2.1 (stream w) (W + e.1)) 0 (coordVec e.2) =
          windowGain W (stream w) (W + e.1) 0 (coordVec e.2))).card : ℕ) : ℝ≥0∞) := by
    simp only [f]
    rw [Fintype.sum_prod_type, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [A, Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq]
  have hcardI : Fintype.card (Win W k (2 ^ b) × (Fin W × Fin k)) =
      (2 ^ b) ^ (W * k) * (W * k) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    ring
  have h1 : ∑ _i : Win W k (2 ^ b) × (Fin W × Fin k), (2 / 3 : ℝ≥0∞) ≤ f ρ := by
    calc _ ≤ ∑ i, alg.law (A i) := Finset.sum_le_sum (fun i _ => hAp i)
      _ = ∫⁻ ρ, f ρ ∂alg.law := hint.symm
      _ ≤ f ρ := hρ
  rw [hfρ, Finset.sum_const, Finset.card_univ, hcardI, nsmul_eq_mul] at h1
  have h2 : (3 : ℝ≥0∞) * (((2 ^ b) ^ (W * k) * (W * k) : ℕ) * (2 / 3)) ≤
      3 * ((∑ w : Win W k (2 ^ b), (Finset.univ.filter (fun e : Fin W × Fin k =>
        alg.query ρ.1 ρ.2.2 (alg.stateAfter ρ.1 ρ.2.1 (stream w) (W + e.1)) 0 (coordVec e.2) =
          windowGain W (stream w) (W + e.1) 0 (coordVec e.2))).card : ℕ) : ℝ≥0∞) :=
    by gcongr
  have h3 : (3 : ℝ≥0∞) * (((2 ^ b) ^ (W * k) * (W * k) : ℕ) * (2 / 3)) =
      ((2 * (W * k) * (2 ^ b) ^ (W * k) : ℕ) : ℝ≥0∞) := by
    have h32 : (3 : ℝ≥0∞) * (2 / 3) = 2 := by
      rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
        mul_one]
    rw [mul_left_comm, h32]
    push_cast
    ring
  rw [h3] at h2
  exact_mod_cast h2

def runZ (p : alg.Public) (ξ : ℕ → alg.Private) (W : ℕ) : ℕ → (Fin M → Bool) → (Fin M → Bool)
  | 0, s => s
  | m + 1, s => alg.update p (ξ (W + m + 1)) (runZ p ξ W m s) (0, 0)

theorem state_run {b : ℕ} (p : alg.Public) (ξ : ℕ → alg.Private) (W : ℕ)
    (w : Win W k (2 ^ b)) (q : ℕ) :
    alg.stateAfter p ξ (stream w) (W + q) = runZ alg p ξ W q (alg.stateAfter p ξ (stream w) W) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    show alg.update p (ξ (W + q + 1)) (alg.stateAfter p ξ (stream w) (W + q)) (stream w (W + q)) =
      alg.update p (ξ (W + q + 1)) (runZ alg p ξ W q (alg.stateAfter p ξ (stream w) W)) (0, 0)
    rw [ih, stream_ge w (W + q) (by omega)]

theorem part3_core (W k b M : ℕ) (hW : 0 < W) (hk : 0 < k) (hb : 0 < b)
    (alg : RandomizedStreamAlgorithm k M)
    (h : ∀ x : ℕ → StreamRow k, (∀ n, RestrictedRow b (x n)) →
        ∀ t, W ≤ t → ∀ j : Fin k,
          (2 / 3 : ℝ≥0∞) ≤ alg.probAnswer x t 0 (coordVec j) (windowGain W x t 0 (coordVec j))) :
    W * k * b ≤ 64 * M := by
  obtain ⟨ρ, hρ⟩ := exists_good_rho alg W b hW h
  refine det_main W k b M hW hk hb
    (fun w => alg.stateAfter ρ.1 ρ.2.1 (stream w) W)
    (fun e s => alg.query ρ.1 ρ.2.2 (runZ alg ρ.1 ρ.2.1 W e.1 s) 0 (coordVec e.2)) ?_
  simpa only [state_run] using hρ

end prob

theorem part3 (W k b : ℕ) (hW : 0 < W) (hk : 0 < k) (hb : 0 < b) :
    ∀ (M : ℕ) (alg : RandomizedStreamAlgorithm k M),
      (∀ x : ℕ → StreamRow k, (∀ n, RestrictedRow b (x n)) →
        ∀ t, W ≤ t → ∀ j : Fin k,
          (2 / 3 : ℝ≥0∞) ≤ alg.probAnswer x t 0 (coordVec j) (windowGain W x t 0 (coordVec j))) →
      ((W * k * b : ℕ) : ℝ) * (1 - Real.binEntropy (1 / 10) / Real.log 2) ≤ 64 * (M : ℝ) := by
  intro M alg h
  have h1 := part3_core W k b M hW hk hb alg h
  have h2 : (0 : ℝ) ≤ Real.binEntropy (1 / 10) / Real.log 2 :=
    div_nonneg (Real.binEntropy_nonneg (by norm_num) (by norm_num))
      (Real.log_nonneg (by norm_num))
  have h3 : ((W * k * b : ℕ) : ℝ) ≤ 64 * (M : ℝ) := by exact_mod_cast h1
  have h4 : (0 : ℝ) ≤ ((W * k * b : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

end TRS.Dev.WindowPart3
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary
open TightReleaseSchedules.Stationary.Supplement

namespace TRS

theorem chk_exact_window_memory (W k b : ℕ) (hW : 0 < W) (hk : 0 < k) (hb : 0 < b) :
    (∀ A : Fin (k + 1) → Finset ℝ, (∀ c, (A c).card ≤ 2 ^ b) →
      ∃ alg : StreamAlgorithm k,
        (∀ x : ℕ → StreamRow k, (∀ n, RowInAlphabet (fun c => (A c : Set ℝ)) (x n)) →
          ∀ t, W ≤ t → ∀ ω ω' : Fin k → ℝ,
            alg.query (alg.stateAfter x t) ω ω' = windowGain W x t ω ω') ∧
        (alg.reachable (RowInAlphabet (fun c => (A c : Set ℝ)))).encard ≤
          (2 ^ (W * (k + 1) * b + Nat.clog 2 W + Nat.clog 2 (W + 1)) : ℕ)) ∧
    (∀ alg : StreamAlgorithm k,
      (∀ x : ℕ → StreamRow k, (∀ n, RestrictedRow b (x n)) →
        ∀ t, W ≤ t → ∀ j : Fin k,
          alg.query (alg.stateAfter x t) 0 (coordVec j) = windowGain W x t 0 (coordVec j)) →
      ((2 ^ (W * k * b) : ℕ) : ℕ∞) ≤ (alg.reachable (RestrictedRow b)).encard) ∧
    (∀ (M : ℕ) (alg : RandomizedStreamAlgorithm k M),
      (∀ x : ℕ → StreamRow k, (∀ n, RestrictedRow b (x n)) →
        ∀ t, W ≤ t → ∀ j : Fin k,
          (2 / 3 : ℝ≥0∞) ≤ alg.probAnswer x t 0 (coordVec j) (windowGain W x t 0 (coordVec j))) →
      ((W * k * b : ℕ) : ℝ) * (1 - Real.binEntropy (1 / 10) / Real.log 2) ≤ 64 * (M : ℝ)) ∧
    (W * (k + 1) * b + Nat.clog 2 W + Nat.clog 2 (W + 1) ≤ 4 * (W * k * b)) := by
  refine ⟨fun A hA => TRS.Dev.WindowPart1.part1 W k b A hA, fun alg h => ?_, ?_, ?_⟩
  · exact TRS.Dev.WindowPart1.part2 W k b alg h
  · exact TRS.Dev.WindowPart3.part3 W k b hW hk hb
  · exact TRS.Dev.WindowPart1.part4 W k b hk hb

end TRS
end

theorem solution : type_of% @TRS.chk_exact_window_memory := @TRS.chk_exact_window_memory
