-- Prove2me | solution 1 for Sennott1989.AvgCost.proposition_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:09:42.82232+00:00
-- url     : https://prove2.me/submissions/684ae8ea-95ea-49aa-8046-43e973e8cc79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions
import Definitions.Def_Sennott1989_AvgCost_Queue
import Theorems.Thm_Sennott1989_AvgCost_queue_drift_14
import Theorems.Thm_SennottDP_MarkovCost_lyapunov_positive_recurrent
import Theorems.Thm_SennottDP_MarkovCost_z_standard_average_cost
import Theorems.Thm_Sennott1989_AvgCost_corollary_prop_5
import Theorems.Thm_Sennott1989_AvgCost_proposition_5_ii
import Theorems.Thm_SennottDP_Discounted_supersolution_ge_stationary_cost
import Theorems.Thm_SennottDP_Discounted_value_function_min_solution_doe
import Theorems.Thm_Sennott1989_AvgCost_theorem_i
import Theorems.Thm_Sennott1989_AvgCost_theorem_ii
import Theorems.Thm_Sennott1989_AvgCost_lemma_limit_point
import Theorems.Thm_Sennott1989_AvgCost_queue_value_monotone

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott8Aux

open SennottDP.Discounted Sennott1989.AvgCost

variable {Act : Type} [Fintype Act] [Nonempty Act]

lemma rate_pos' (q : QueueData Act) (x : Act) : 0 < q.rate x := by
  unfold QueueData.rate; exact ENNReal.ofReal_pos.2 (q.rate_pos x)

lemma rate_lt_one' (q : QueueData Act) (x : Act) : q.rate x < 1 := by
  unfold QueueData.rate
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (q.rate_lt_one x)

lemma one_sub_rate_pos (q : QueueData Act) (x : Act) : 0 < 1 - q.rate x :=
  tsub_pos_of_lt (rate_lt_one' q x)

lemma trans_down (q : QueueData Act) (x : Act) (i : ℕ) (hi : 1 ≤ i) :
    q.trans i x (i - 1) = q.rate x * (q.p 0 : ℝ≥0∞) := by
  have e1 : ¬ (i - 1 + 1 < i) := by omega
  have e2 : i - 1 + 1 - i = 0 := by omega
  simp [QueueData.trans, show i ≠ 0 by omega, e1, e2, QueueData.pPrev]

lemma trans_up (q : QueueData Act) (x : Act) (i m : ℕ) (hi : 1 ≤ i) :
    q.trans i x (i + m) =
      q.rate x * (q.p (m + 1) : ℝ≥0∞) + (1 - q.rate x) * (q.p m : ℝ≥0∞) := by
  have e1 : ¬ (i + m + 1 < i) := by omega
  have e2 : i + m + 1 - i = m + 1 := by omega
  simp [QueueData.trans, show i ≠ 0 by omega, e1, e2, QueueData.pPrev]

/-- one-step reachability -/
def Edge (Γ : SennottDP.MarkovCost.MC ℕ) (i j : ℕ) : Prop := 0 < Γ.P i j

lemma leadsTo_of_rtg (Γ : SennottDP.MarkovCost.MC ℕ) {i j : ℕ}
    (h : Relation.ReflTransGen (Edge Γ) i j) : SennottDP.MarkovCost.LeadsTo Γ i j := by
  induction h with
  | refl => exact ⟨0, by simp [SennottDP.MarkovCost.nStep]⟩
  | tail _ hbc ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + 1, ?_⟩
    simp only [SennottDP.MarkovCost.nStep]
    exact lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt ht) (ne_of_gt hbc)) (ENNReal.le_tsum _)


/-- the constant stationary policy -/
def constPol (q : QueueData Act) (x : Act) : StationaryPolicy q.toMDC :=
  ⟨fun _ => x, fun _ => Finset.mem_univ _⟩

lemma chainP (q : QueueData Act) (x : Act) (i j : ℕ) :
    (inducedChain q.toMDC (constPol q x)).P i j = q.trans i x j := rfl

lemma irreducible_const (q : QueueData Act) (x : Act) (hp0 : 0 < q.p 0) (m : ℕ) (hm : 1 ≤ m)
    (hpm : 0 < q.p m) :
    SennottDP.MarkovCost.Irreducible (inducedChain q.toMDC (constPol q x)) := by
  set Γ := inducedChain q.toMDC (constPol q x)
  have hp0' : (0 : ℝ≥0∞) < (q.p 0 : ℝ≥0∞) := by exact_mod_cast hp0
  have hpm' : (0 : ℝ≥0∞) < (q.p m : ℝ≥0∞) := by exact_mod_cast hpm
  have down : ∀ i, 1 ≤ i → Edge Γ i (i - 1) := by
    intro i hi
    show 0 < q.trans i x (i - 1)
    rw [trans_down q x i hi]
    exact ENNReal.mul_pos (ne_of_gt (rate_pos' q x)) (ne_of_gt hp0')
  have up : ∀ i, 1 ≤ i → Edge Γ i (i + m) := by
    intro i hi
    show 0 < q.trans i x (i + m)
    rw [trans_up q x i m hi]
    exact lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt (one_sub_rate_pos q x)) (ne_of_gt hpm'))
      le_add_self
  have zero_up : Edge Γ 0 m := by
    show 0 < q.trans 0 x m
    simpa [QueueData.trans] using hpm'
  have to_below : ∀ j d, Relation.ReflTransGen (Edge Γ) (j + d) j := by
    intro j d
    induction d with
    | zero => exact Relation.ReflTransGen.refl
    | succ d ih =>
      have := down (j + (d + 1)) (by omega)
      rw [show j + (d + 1) - 1 = j + d by omega] at this
      exact Relation.ReflTransGen.head this ih
  have from_zero : ∀ k, Relation.ReflTransGen (Edge Γ) 0 (m + k * m) := by
    intro k
    induction k with
    | zero => simpa using Relation.ReflTransGen.single zero_up
    | succ k ih =>
      have := up (m + k * m) (by omega)
      rw [show m + k * m + m = m + (k + 1) * m by ring] at this
      exact ih.tail this
  have reach : ∀ i j, Relation.ReflTransGen (Edge Γ) i j := by
    intro i j
    have h1 : Relation.ReflTransGen (Edge Γ) i 0 := by simpa using to_below 0 i
    have h2 := from_zero j
    have hle : j ≤ m + j * m := by nlinarith
    have h3 := to_below j (m + j * m - j)
    rw [show j + (m + j * m - j) = m + j * m by omega] at h3
    exact h1.trans (h2.trans h3)
  intro i j
  exact ⟨leadsTo_of_rtg Γ (reach i j), leadsTo_of_rtg Γ (reach j i)⟩

lemma conv_tsum (P : ℕ → ℝ≥0∞) (hP : ∑' j, P j = 1) (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (c : ℝ)
    (hs : Summable fun j => (P j).toReal * (g j - c)) :
    ∑' j, P j * ENNReal.ofReal (g j) =
      ENNReal.ofReal (∑' j, (P j).toReal * (g j - c) + c) := by
  have hfin : ∀ j, P j ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hP ▸ ENNReal.le_tsum (f := P) j)
  have hsP : Summable fun j => (P j).toReal := ENNReal.summable_toReal (by rw [hP]; simp)
  have htP : ∑' j, (P j).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hfin, hP]; simp
  have hsc : Summable fun j => (P j).toReal * c := hsP.mul_right c
  have hsg : Summable fun j => (P j).toReal * g j := by
    have := hs.add hsc
    refine this.congr fun j => ?_
    ring
  have heq : ∑' j, (P j).toReal * g j = ∑' j, (P j).toReal * (g j - c) + c := by
    have : (fun j => (P j).toReal * g j) = fun j => (P j).toReal * (g j - c) + (P j).toReal * c := by
      funext j; ring
    rw [this, hs.tsum_add hsc, tsum_mul_right, htP, one_mul]
  rw [← heq, ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg (hg j)) hsg]
  refine tsum_congr fun j => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin j)]

lemma tsum_p_ofReal_lt_top (q : QueueData Act) (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j)
    (hs : Summable fun j => (q.p j : ℝ) * g j) :
    ∑' j, (q.p j : ℝ≥0∞) * ENNReal.ofReal (g j) < ⊤ := by
  have : ∑' j, (q.p j : ℝ≥0∞) * ENNReal.ofReal (g j) = ENNReal.ofReal (∑' j, (q.p j : ℝ) * g j) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (f := fun j => (q.p j : ℝ) * g j)
      (fun j => mul_nonneg (q.p j).2 (hg j)) hs]
    refine tsum_congr fun j => ?_
    rw [ENNReal.ofReal_mul NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
  rw [this]; exact ENNReal.ofReal_lt_top

lemma summable_pow_le (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ q.n + 1) :
    Summable fun i : ℕ => (q.p i : ℝ) * (i : ℝ) ^ k := by
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (q.p i).2 (by positivity)) (fun i => ?_) hmom
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [zero_pow (by omega : k ≠ 0)]
  · have h1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have := pow_le_pow_right₀ h1 hk
    nlinarith [(q.p i).2]

lemma p0_pos (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) (x : Act)
    (hx : q.lam < q.a x * q.β) : 0 < q.p 0 := by
  by_contra hne
  have h : (0 : ℝ≥0) = q.p 0 := (le_antisymm (not_lt.1 hne) bot_le).symm
  have hs1 := summable_pow_le q hmom 1 le_rfl (by omega)
  have hsp : Summable fun i => (q.p i : ℝ) := (NNReal.hasSum_coe.2 q.p_hasSum).summable
  have htp : ∑' i, (q.p i : ℝ) = 1 := (NNReal.hasSum_coe.2 q.p_hasSum).tsum_eq.trans (by simp)
  have hle : ∑' i, (q.p i : ℝ) ≤ q.lam := by
    unfold QueueData.lam QueueData.moment
    refine hsp.tsum_le_tsum (fun i => ?_) (hs1.congr fun i => by ring)
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [← h]
    · have h1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
      simp only [pow_one]; nlinarith [(q.p i).2]
  linarith [q.rate_lt_one x]

/-- the same queue with holding cost `Q = 1` of degree `0` (same transitions) -/
noncomputable def linQ (q : QueueData Act) : QueueData Act :=
  { q with
    n := 0
    Q := Polynomial.C 1
    Q_degree := (by simp)
    Q_nonneg := (by simp)
    Q_mono := fun _ _ _ => by simp }

@[simp] lemma linQ_n (q : QueueData Act) : (linQ q).n = 0 := rfl

lemma lam_nonneg (q : QueueData Act) : 0 ≤ q.lam := by
  unfold QueueData.lam QueueData.moment
  exact tsum_nonneg fun i => mul_nonneg (by positivity) (q.p i).2

lemma posrec_const (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) (x : Act)
    (hx : q.lam < q.a x * q.β)
    (hirr : SennottDP.MarkovCost.Irreducible (inducedChain q.toMDC (constPol q x))) :
    ∀ j, SennottDP.MarkovCost.PositiveRecurrent (inducedChain q.toMDC (constPol q x)) j := by
  set Γ := inducedChain q.toMDC (constPol q x)
  set d := q.a x * q.β - q.lam with hd
  have hdpos : 0 < d := by linarith
  have hd1 : d < 1 := by linarith [q.rate_lt_one x, lam_nonneg q]
  set c := 1 / d with hc
  have hc1 : 1 ≤ c := by rw [hc, le_div_iff₀ hdpos]; linarith
  have hs1 := summable_pow_le q hmom 1 le_rfl (by omega)
  have hmom' : Summable fun i : ℕ => (i : ℝ) ^ ((linQ q).n + 1) * ((linQ q).p i : ℝ) := by
    refine hs1.congr fun i => ?_
    show (q.p i : ℝ) * (i : ℝ) ^ 1 = (i : ℝ) ^ (0 + 1) * (q.p i : ℝ)
    ring
  obtain ⟨P, hdeg, hcoef, hdr⟩ := queue_drift_14 (linQ q) hmom' x c
  have hPc : ∀ t : ℝ, P.eval t = -1 := by
    intro t
    rw [Polynomial.eq_C_of_natDegree_le_zero hdeg, Polynomial.eval_C]
    have : (linQ q).n = 0 := rfl
    rw [this] at hcoef
    rw [hcoef]
    show c * ((0 : ℕ) + 1 : ℝ) * (q.lam - q.a x * q.β) = -1
    simp only [Nat.cast_zero, zero_add, mul_one]
    rw [hc, show q.lam - q.a x * q.β = -d by rw [hd]; ring]
    field_simp
  let y : ℕ → ℝ≥0 := fun j => Real.toNNReal (c * j)
  have hdrift : ∀ i, i ≠ 0 → ∑' j, Γ.P i j * (y j : ℝ≥0∞) + ((1 : ℝ≥0) : ℝ≥0∞) ≤ y i := by
    intro i hi
    obtain ⟨hsum, heq⟩ := hdr i (by omega)
    have hs' : Summable fun j => (q.trans i x j).toReal * (c * j - c * i) := by
      refine hsum.congr fun j => ?_
      show (q.trans i x j).toReal * (c * (j : ℝ) ^ (0 + 1) - c * (i : ℝ) ^ (0 + 1)) = _
      simp
    have heq' : ∑' j, (q.trans i x j).toReal * (c * j - c * i) = -1 := by
      rw [← hPc i, ← heq]
      refine tsum_congr fun j => ?_
      show _ = (q.trans i x j).toReal * (c * (j : ℝ) ^ (0 + 1) - c * (i : ℝ) ^ (0 + 1))
      simp
    have hconv := conv_tsum (q.trans i x) (q.trans_sum i x) (fun j => c * j)
      (fun j => by positivity) (c * i) hs'
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
    show ∑' j, q.trans i x j * ENNReal.ofReal (c * j) + ((1 : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal (c * i)
    rw [hconv, heq', ENNReal.coe_one, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by nlinarith) zero_le_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hz : ∑' j, Γ.P 0 j * (y j : ℝ≥0∞) < ⊤ := by
    show ∑' j, q.trans 0 x j * ENNReal.ofReal (c * j) < ⊤
    simp only [QueueData.trans, if_true]
    exact tsum_p_ofReal_lt_top q _ (fun j => by positivity)
      ((hs1.mul_left c).congr fun j => by ring)
  obtain ⟨_, hmean, hmean0, _⟩ :=
    SennottDP.MarkovCost.lyapunov_positive_recurrent Γ 0 y 1 one_pos hz hdrift
  have hstd : SennottDP.MarkovCost.IsZStandard Γ (fun _ => 0) 0 := by
    intro i
    refine ⟨?_, ?_⟩
    · by_cases hi : i = 0
      · subst hi; exact hmean0
      · exact lt_of_le_of_lt (hmean i hi) (by simp)
    · simp [SennottDP.MarkovCost.passageCost]
  obtain ⟨R, hR, -, -, -, -⟩ := SennottDP.MarkovCost.z_standard_average_cost Γ _ 0 hstd
  obtain ⟨⟨i0, hRi⟩, hRp⟩ := hR
  intro j
  exact hRp j (by rw [hRi]; exact hirr i0 j)

lemma conv_nonneg (P : ℕ → ℝ≥0∞) (hP : ∑' j, P j = 1) (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (c : ℝ)
    (hs : Summable fun j => (P j).toReal * (g j - c)) :
    0 ≤ ∑' j, (P j).toReal * (g j - c) + c := by
  have h := conv_tsum P hP g hg c hs
  by_contra hneg
  push Not at hneg
  rw [ENNReal.ofReal_of_nonpos hneg.le, ENNReal.tsum_eq_zero] at h
  have hsP : Summable fun j => (P j).toReal := ENNReal.summable_toReal (by rw [hP]; simp)
  have hfin : ∀ j, P j ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hP ▸ ENNReal.le_tsum (f := P) j)
  have htP : ∑' j, (P j).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hfin, hP]; simp
  have hsc : Summable fun j => (P j).toReal * c := hsP.mul_right c
  have heq : ∑' j, (P j).toReal * (g j - c) + c = ∑' j, (P j).toReal * g j := by
    have : (fun j => (P j).toReal * g j) = fun j => (P j).toReal * (g j - c) + (P j).toReal * c := by
      funext j; ring
    rw [this, hs.tsum_add hsc, tsum_mul_right, htP, one_mul]
  have : ∑' j, (P j).toReal * g j = 0 := by
    refine (tsum_congr fun j => ?_).trans tsum_zero
    have := h j
    rcases mul_eq_zero.1 this with h0 | h0
    · simp [h0]
    · rw [ENNReal.ofReal_eq_zero] at h0
      simp [le_antisymm h0 (hg j)]
  linarith

lemma poly_ev_neg (R : Polynomial ℝ) (n : ℕ) (hdeg : R.natDegree ≤ n) (hc : R.coeff n < 0) :
    ∃ N : ℕ, ∀ i : ℕ, N < i → R.eval (i : ℝ) ≤ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, fun i _ => ?_⟩
    rw [Polynomial.eq_C_of_natDegree_le_zero hdeg, Polynomial.eval_C]; exact hc.le
  · have hnd : R.natDegree = n := le_antisymm hdeg (Polynomial.le_natDegree_of_ne_zero hc.ne)
    have hR0 : R ≠ 0 := by rintro rfl; simp at hc
    have hdeg' : 0 < R.degree := by
      rw [Polynomial.degree_eq_natDegree hR0, hnd]; exact_mod_cast hn
    have hlc : R.leadingCoeff ≤ 0 := by
      rw [Polynomial.leadingCoeff, hnd]; exact hc.le
    have ht := (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos R hdeg' hlc).comp
      tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (eventually_le_atBot 0))
    exact ⟨N, fun i hi => hN i hi.le⟩

lemma drift_const (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) (x : Act)
    (hx : q.lam < q.a x * q.β) :
    ∃ (N : ℕ) (r : ℕ → ℝ≥0), (∀ i, i ≤ N → ∑' j, q.trans i x j * (r j : ℝ≥0∞) < ⊤) ∧
      ∀ i, N < i → ∑' j, q.trans i x j * (r j : ℝ≥0∞) + (q.cost i x : ℝ≥0∞) ≤ (r i : ℝ≥0∞) := by
  set d := q.a x * q.β - q.lam with hd
  have hdpos : 0 < d := by linarith
  set cQ := q.Q.coeff q.n
  set b := q.B x
  have hb := q.B_pos x
  have hn1 : (0 : ℝ) < (q.n : ℝ) + 1 := by positivity
  set A := (|cQ| + b + 1) / (((q.n : ℝ) + 1) * d) with hA
  have hApos : 0 < A := by rw [hA]; apply div_pos (by positivity) (by positivity)
  obtain ⟨P, hdeg, hcoef, hdr⟩ := queue_drift_14 q hmom x A
  have hPn : P.coeff q.n = -(|cQ| + b + 1) := by
    rw [hcoef, hA, show q.lam - q.a x * q.β = -d by rw [hd]; ring]
    field_simp
  set R := P + q.Q + Polynomial.C b
  have hQn : q.Q.natDegree = q.n := Polynomial.natDegree_eq_of_degree_eq_some q.Q_degree
  have hRdeg : R.natDegree ≤ q.n := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_add_le _ _).trans (max_le hdeg hQn.le)
    · simp
  have hCb : (Polynomial.C b).coeff q.n ≤ b := by
    rw [Polynomial.coeff_C]; split_ifs <;> linarith
  have hRc : R.coeff q.n < 0 := by
    simp only [R, Polynomial.coeff_add]
    rw [hPn]
    have := le_abs_self cQ
    linarith
  obtain ⟨N, hN⟩ := poly_ev_neg R q.n hRdeg hRc
  let g : ℕ → ℝ := fun j => A * (j : ℝ) ^ (q.n + 1)
  have hg : ∀ j, 0 ≤ g j := fun j => by positivity
  refine ⟨N, fun j => Real.toNNReal (g j), ?_, ?_⟩
  · intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · show ∑' j, q.trans 0 x j * ENNReal.ofReal (g j) < ⊤
      simp only [QueueData.trans, if_true]
      exact tsum_p_ofReal_lt_top q g hg
        (((summable_pow_le q hmom (q.n + 1) (by omega) le_rfl).mul_left A).congr fun j => by
          simp only [g]; ring)
    · obtain ⟨hs, _⟩ := hdr i hi
      show ∑' j, q.trans i x j * ENNReal.ofReal (g j) < ⊤
      rw [conv_tsum (q.trans i x) (q.trans_sum i x) g hg (g i) hs]
      exact ENNReal.ofReal_lt_top
  · intro i hi
    have hi1 : 1 ≤ i := by omega
    obtain ⟨hs, heq⟩ := hdr i hi1
    have hnn := conv_nonneg (q.trans i x) (q.trans_sum i x) g hg (g i) hs
    show ∑' j, q.trans i x j * ENNReal.ofReal (g j) + (q.cost i x : ℝ≥0∞) ≤ ENNReal.ofReal (g i)
    rw [conv_tsum (q.trans i x) (q.trans_sum i x) g hg (g i) hs]
    have hc : (q.cost i x : ℝ≥0∞) = ENNReal.ofReal (q.Q.eval (i : ℝ) + b) := by
      simp [QueueData.cost, show i ≠ 0 by omega, b, ENNReal.ofReal]
    have hQi := q.Q_nonneg i
    rw [hc, ← ENNReal.ofReal_add hnn (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    have := hN i hi
    simp only [R, Polynomial.eval_add, Polynomial.eval_C] at this
    have heq' : ∑' j, (q.trans i x j).toReal * (g j - g i) = P.eval (i : ℝ) := heq
    rw [heq']
    linarith

section Degenerate

variable (q : QueueData Act) (hdeg : ∀ m, 1 ≤ m → q.p m = 0)
include hdeg

lemma deg_p0 : q.p 0 = 1 := by
  have h : HasSum q.p (q.p 0) := hasSum_single 0 (fun m hm => hdeg m (by omega))
  exact h.unique q.p_hasSum

lemma deg_trans_zero (x : Act) (W : ℕ → ℝ≥0∞) : ∑' j, q.trans 0 x j * W j = W 0 := by
  rw [tsum_eq_single 0]
  · simp [QueueData.trans, deg_p0 q hdeg]
  · intro j hj
    simp [QueueData.trans, hdeg j (by omega)]

lemma deg_trans_succ (x : Act) (W : ℕ → ℝ≥0∞) (i : ℕ) :
    ∑' j, q.trans (i + 1) x j * W j = q.rate x * W i + (1 - q.rate x) * W (i + 1) := by
  have hp0 := deg_p0 q hdeg
  rw [tsum_eq_sum (s := {i, i + 1})]
  · rw [Finset.sum_pair (by omega)]
    have e1 : q.trans (i + 1) x i = q.rate x := by
      simp [QueueData.trans, QueueData.pPrev, hp0]
    have e2 : q.trans (i + 1) x (i + 1) = 1 - q.rate x := by
      have : i + 1 + 1 - (i + 1) = 1 := by omega
      simp [QueueData.trans, QueueData.pPrev, hp0, this, hdeg 1 le_rfl]
    rw [e1, e2]
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    by_cases hlt : j + 1 < i + 1
    · simp [QueueData.trans, hlt]
    · have hk : 2 ≤ j + 1 - (i + 1) := by omega
      have h1 : q.p (j - i) = 0 := hdeg _ (by omega)
      have h2 : q.pPrev (j - i) = 0 := by
        unfold QueueData.pPrev
        rw [if_neg (by omega)]; exact hdeg _ (by omega)
      simp [QueueData.trans, hlt, h1, h2]

lemma deg_assumptions : Assumption1 q.toMDC ∧ ∃ Mb : ℕ → ℝ, Assumption3Star q.toMDC Mb := by
  classical
  obtain x0 : Act := Classical.arbitrary Act
  set ρ := q.a x0 * q.β with hρ
  have hρ0 : 0 < ρ := q.rate_pos x0
  have hρ1 : ρ < 1 := q.rate_lt_one x0
  set Q0 := q.Q.eval 0
  have hQ0 : 0 ≤ Q0 := by simpa using q.Q_nonneg 0
  let K : ℕ → ℝ := fun k => q.Q.eval (k : ℝ) + q.B x0
  have hK : ∀ k, 0 ≤ K k := fun k => by have := q.Q_nonneg k; have := q.B_pos x0; simp only [K]; linarith
  let D : ℕ → ℝ := fun i => ∑ k ∈ Finset.range i, K (k + 1) / ρ
  have hD : ∀ i, 0 ≤ D i := fun i => Finset.sum_nonneg fun k _ => div_nonneg (hK _) hρ0.le
  have hDs : ∀ i, D (i + 1) = D i + K (i + 1) / ρ := fun i => Finset.sum_range_succ _ _
  have hrate : q.rate x0 = ENNReal.ofReal ρ := rfl
  have h1r : 1 - q.rate x0 = ENNReal.ofReal (1 - ρ) := by
    rw [hrate, ENNReal.ofReal_sub _ hρ0.le, ENNReal.ofReal_one]
  -- the supersolution
  have key : ∀ α : ℝ≥0, 0 < α → α < 1 →
      (∀ i, valueFn q.toMDC α i ≤ ENNReal.ofReal (Q0 / (1 - α) + D i)) ∧
        (valueFn q.toMDC α 0).toReal = Q0 / (1 - α) := by
    intro α hα0 hα1
    have ha1 : (α : ℝ) < 1 := by exact_mod_cast hα1
    have ha0 : (0 : ℝ) ≤ α := α.2
    have h1a : 0 < 1 - (α : ℝ) := by linarith
    have hαe : (α : ℝ≥0∞) = ENNReal.ofReal α := (ENNReal.ofReal_coe_nnreal).symm
    set W : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (Q0 / (1 - α) + D i)
    have hW0 : 0 ≤ Q0 / (1 - α) := div_nonneg hQ0 h1a.le
    have hsup : ∀ i, bellmanQ q.toMDC α W i ((constPol q x0).1 i) ≤ W i := by
      intro i
      show (q.cost i x0 : ℝ≥0∞) + (α : ℝ≥0∞) * ∑' j, q.trans i x0 j * W j ≤ W i
      rcases i with _ | i
      · rw [deg_trans_zero q hdeg]
        have hc : (q.cost 0 x0 : ℝ≥0∞) = ENNReal.ofReal Q0 := by
          simp [QueueData.cost, Q0, ENNReal.ofReal]
        simp only [W, hc, hαe]
        have hD0 : D 0 = 0 := by simp [D]
        rw [hD0, add_zero, ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_add hQ0 (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [le_div_iff₀ h1a]
        have : (α : ℝ) * (Q0 / (1 - α)) * (1 - α) = α * Q0 := by field_simp
        nlinarith
      · rw [deg_trans_succ q hdeg]
        have hc : (q.cost (i + 1) x0 : ℝ≥0∞) = ENNReal.ofReal (K (i + 1)) := by
          simp [QueueData.cost, K, ENNReal.ofReal]
        rw [h1r]
        simp only [W, hc, hαe, hrate]
        have hw0 : 0 ≤ Q0 / (1 - α) + D i := by linarith [hD i]
        have hw1 : 0 ≤ Q0 / (1 - α) + D (i + 1) := by linarith [hD (i + 1)]
        rw [← ENNReal.ofReal_mul hρ0.le, ← ENNReal.ofReal_mul (by linarith),
          ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by linarith) hw1),
          ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_add (hK _) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        set w0 := Q0 / (1 - α) + D i
        set w1 := Q0 / (1 - α) + D (i + 1)
        have hw : w1 = w0 + K (i + 1) / ρ := by simp only [w0, w1, hDs]; ring
        have hmix : ρ * w0 + (1 - ρ) * w1 = w1 - K (i + 1) := by
          rw [hw]; field_simp; ring
        have hKle : K (i + 1) ≤ w1 := by
          rw [hw]
          have : K (i + 1) ≤ K (i + 1) / ρ := by
            rw [le_div_iff₀ hρ0]; nlinarith [hK (i + 1)]
          linarith [hD i]
        rw [hmix]
        nlinarith [mul_nonneg h1a.le (sub_nonneg.2 hKle)]
    obtain ⟨-, hdisc⟩ := SennottDP.Discounted.supersolution_ge_stationary_cost q.toMDC α hα0 hα1 W
      (constPol q x0) hsup
    have hV : ∀ i, valueFn q.toMDC α i ≤ W i := fun i =>
      (iInf_le _ (constPol q x0).toPolicy).trans (hdisc i)
    refine ⟨hV, ?_⟩
    obtain ⟨hdoe, -, -⟩ := SennottDP.Discounted.value_function_min_solution_doe q.toMDC α hα0 hα1
    set V := valueFn q.toMDC α
    have hQa : ∀ a, bellmanQ q.toMDC α V 0 a = ENNReal.ofReal Q0 + (α : ℝ≥0∞) * V 0 := by
      intro a
      show (q.cost 0 a : ℝ≥0∞) + (α : ℝ≥0∞) * ∑' j, q.trans 0 a j * V j = _
      rw [deg_trans_zero q hdeg]
      simp [QueueData.cost, Q0, ENNReal.ofReal]
    have hb : V 0 = ENNReal.ofReal Q0 + (α : ℝ≥0∞) * V 0 := by
      conv_lhs => rw [hdoe 0]
      apply le_antisymm
      · exact (Finset.inf'_le _ (Finset.mem_univ x0)).trans (hQa x0).le
      · exact Finset.le_inf' _ _ fun a _ => (hQa a).ge
    have hfin : V 0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV 0)
    have hb' := congrArg ENNReal.toReal hb
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin),
      ENNReal.toReal_ofReal hQ0, ENNReal.toReal_mul] at hb'
    simp only [ENNReal.coe_toReal] at hb'
    rw [eq_div_iff h1a.ne']
    linarith
  refine ⟨fun α hα0 hα1 i => lt_of_le_of_lt ((key α hα0 hα1).1 i) ENNReal.ofReal_lt_top, D, ?_, ?_⟩
  · have hfinsum : ∀ i, ∀ a ∈ q.toMDC.A i,
        ∑' j, q.toMDC.P i a j * ENNReal.ofReal (D j) < ⊤ := by
      intro i a _
      show ∑' j, q.trans i a j * ENNReal.ofReal (D j) < ⊤
      rcases i with _ | i
      · rw [deg_trans_zero q hdeg]; exact ENNReal.ofReal_lt_top
      · rw [deg_trans_succ q hdeg]
        exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ((rate_lt_one' q a).trans ENNReal.one_lt_top)
          ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ((tsub_le_self).trans_lt ENNReal.one_lt_top)
          ENNReal.ofReal_lt_top⟩
    refine ⟨hD, ?_, fun i => ⟨x0, Finset.mem_univ _, hfinsum i x0 (Finset.mem_univ _)⟩⟩
    intro α hα0 hα1 i
    obtain ⟨hV, hV0⟩ := key α hα0 hα1
    unfold relValue
    rw [hV0]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hV i)
    rw [ENNReal.toReal_ofReal (by linarith [hD i, div_nonneg hQ0 (by
      have : (α : ℝ) < 1 := by exact_mod_cast hα1
      linarith : (0:ℝ) ≤ 1 - α)])] at this
    linarith
  · intro i a ha
    show ∑' j, q.trans i a j * ENNReal.ofReal (D j) < ⊤
    rcases i with _ | i
    · rw [deg_trans_zero q hdeg]; exact ENNReal.ofReal_lt_top
    · rw [deg_trans_succ q hdeg]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ((rate_lt_one' q a).trans ENNReal.one_lt_top)
        ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ((tsub_le_self).trans_lt ENNReal.one_lt_top)
        ENNReal.ofReal_lt_top⟩

end Degenerate

lemma nondeg_data (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ))
    (hdg : ¬ ∀ m, 1 ≤ m → q.p m = 0) (x : Act) (hx : q.lam < q.a x * q.β) :
    SennottDP.MarkovCost.Irreducible (inducedChain q.toMDC (constPol q x)) ∧
      GoodPolicy q.toMDC (constPol q x) := by
  push Not at hdg
  obtain ⟨m, hm, hpm⟩ := hdg
  have hirr := irreducible_const q x (p0_pos q hmom x hx) m hm (pos_iff_ne_zero.2 hpm)
  refine ⟨hirr, ⟨hirr, posrec_const q hmom x hx hirr⟩, Or.inr (Or.inr ?_)⟩
  obtain ⟨N, r, hfin, hdr⟩ := drift_const q hmom x hx
  exact ⟨N, r, hfin, hdr⟩

lemma assm_part1 (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ))
    (hx : ∃ x, q.lam < q.a x * q.β) :
    Assumption1 q.toMDC ∧ ∃ Mb : ℕ → ℝ, Assumption3 q.toMDC Mb := by
  by_cases hdg : ∀ m, 1 ≤ m → q.p m = 0
  · obtain ⟨h1, Mb, h3⟩ := deg_assumptions q hdg
    exact ⟨h1, Mb, h3.1⟩
  · obtain ⟨x, hx⟩ := hx
    have hirr := (nondeg_data q hmom hdg x hx).1
    obtain ⟨N, r, hfin, hdr⟩ := drift_const q hmom x hx
    refine corollary_prop_5 q.toMDC (constPol q x) hirr r N hfin hdr
      ⟨Real.toNNReal (q.B x), Real.toNNReal_pos.2 (q.B_pos x), fun i hi => ?_⟩
    show Real.toNNReal (q.B x) ≤ q.cost i x
    simp only [QueueData.cost, if_neg (show i ≠ 0 by omega)]
    exact Real.toNNReal_le_toNNReal (by linarith [q.Q_nonneg i])

lemma assm_part2 (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ))
    (hx : ∀ x, q.lam < q.a x * q.β) :
    Assumption1 q.toMDC ∧ ∃ Mb : ℕ → ℝ, Assumption3Star q.toMDC Mb := by
  by_cases hdg : ∀ m, 1 ≤ m → q.p m = 0
  · exact deg_assumptions q hdg
  · exact proposition_5_ii q.toMDC fun i a _ =>
      ⟨constPol q a, rfl, (nondeg_data q hmom hdg a (hx a)).2⟩

end Sennott8Aux

open SennottDP.Discounted Sennott1989.AvgCost Sennott8Aux in
theorem solution {Act : Type} [Fintype Act] [Nonempty Act] (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) :
    ((∃ x, q.lam < q.a x * q.β) →
        ∃ (f : StationaryPolicy q.toMDC) (g : ℝ), IsACOptimal q.toMDC f g) ∧
      ((∀ x, q.lam < q.a x * q.β) →
        ∃ (g : ℝ) (h : ℕ → ℝ), IsAbelLimit q.toMDC g ∧
          (∃ f : StationaryPolicy q.toMDC, IsACOptimal q.toMDC f g) ∧
          BddBelow (Set.range h) ∧ ACOE q.toMDC g h) := by
  have hA2 : Assumption1 q.toMDC → Assumption2 q.toMDC 0 := (queue_value_monotone q).2.2
  let αs : ℕ → ℝ≥0 := fun n => ((n + 1 : ℕ) : ℝ≥0) / (((n + 1 : ℕ) : ℝ≥0) + 1)
  have hα0 : ∀ n, 0 < αs n := fun n => div_pos (by positivity) (by positivity)
  have hα1 : ∀ n, αs n < 1 := fun n => (div_lt_one (by positivity)).2 (lt_add_one _)
  have hlim : Tendsto αs atTop (𝓝 1) :=
    (tendsto_natCast_div_add_atTop (1 : ℝ≥0)).comp (tendsto_add_atTop_nat 1)
  have hreal : ∀ α : ℝ≥0, ∃ f : StationaryPolicy q.toMDC, Realizes q.toMDC f α (valueFn q.toMDC α) := by
    intro α
    choose a ha heq using fun i => Finset.exists_mem_eq_inf' (q.toMDC.A_nonempty i)
      (bellmanQ q.toMDC α (valueFn q.toMDC α) i)
    exact ⟨⟨a, ha⟩, fun i => (heq i).symm⟩
  choose fs hfs using fun n => hreal (αs n)
  obtain ⟨f, hf⟩ := lemma_limit_point q.toMDC αs hα0 hα1 hlim fs hfs
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨h1, Mb, h3⟩ := assm_part1 q hmom hx
    obtain ⟨g, -, -, -, -, hopt, -⟩ :=
      theorem_i q.toMDC 0 Mb h1 (hA2 h1) h3 αs hα0 hα1 hlim fs hfs f hf
    exact ⟨f, g, hopt⟩
  · obtain ⟨h1, Mb, h3⟩ := assm_part2 q hmom hx
    obtain ⟨g, h, habel, hb, -, hopt, -, hacoe⟩ :=
      theorem_ii q.toMDC 0 Mb h1 (hA2 h1) h3 αs hα0 hα1 hlim fs hfs f hf
    exact ⟨g, h, habel, ⟨f, hopt⟩, ⟨-0, by rintro _ ⟨i, rfl⟩; exact (hb i).1⟩, hacoe⟩
