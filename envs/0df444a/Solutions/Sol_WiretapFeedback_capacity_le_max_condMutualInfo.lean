-- Prove2me | solution 1 for WiretapFeedback.capacity_le_max_condMutualInfo
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T06:28:14.186885+00:00
-- url     : https://prove2.me/submissions/2496e76f-59e0-4a8b-9536-fbaa984a1c53

import Mathlib
import Definitions.Def_WiretapFeedback_activeBeta
import Definitions.Def_WiretapFeedback_negLog2
import Definitions.Def_WiretapFeedback_condDiv
import Definitions.Def_WiretapFeedback_wiretapCapacity
import Definitions.Def_WiretapFeedback_jointLaw
import Theorems.Thm_WiretapFeedback_logN_le_negLog_activeBeta
import Theorems.Thm_WiretapFeedback_minimax_condDiv_eq_max_condMutualInfo

open scoped ENNReal

namespace StrongConvAux

open WiretapFeedback

variable {X O : Type} [Fintype X] [Fintype O] {n : ℕ}

section Prefix

variable (S : FeedbackStrategy X O n) (ux : S.Ux) (uy : S.Uy)

/-- The input at time `s` produced from a prefix `o` of length `k`. -/
def inp (k : ℕ) (h : k ≤ n) (s : Fin k) (o : Fin k → O) : X :=
  S.inputAt ⟨s.val, lt_of_lt_of_le s.isLt h⟩ ux uy (fun i => o ⟨i.val, lt_trans i.isLt s.isLt⟩)

lemma inp_snoc_castSucc (k : ℕ) (h : k + 1 ≤ n) (s : Fin k) (o' : Fin k → O) (a : O) :
    inp S ux uy (k + 1) h (Fin.castSucc s) (Fin.snoc o' a) =
      inp S ux uy k (Nat.le_of_succ_le h) s o' := by
  unfold inp
  congr 1
  funext i
  have : (⟨i.val, lt_trans i.isLt (Fin.castSucc s).isLt⟩ : Fin (k + 1)) =
      Fin.castSucc ⟨i.val, lt_trans i.isLt s.isLt⟩ := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma inp_snoc_last (k : ℕ) (h : k + 1 ≤ n) (o' : Fin k → O) (a : O) :
    inp S ux uy (k + 1) h (Fin.last k) (Fin.snoc o' a) =
      S.inputAt ⟨k, h⟩ ux uy o' := by
  unfold inp
  congr 1
  funext i
  have : (⟨i.val, lt_trans i.isLt (Fin.last k).isLt⟩ : Fin (k + 1)) =
      Fin.castSucc ⟨i.val, i.isLt⟩ := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

/-- Splitting a sum over `(k+1)`-tuples. -/
lemma sum_snoc {M : Type*} [AddCommMonoid M] (k : ℕ) (f : (Fin (k + 1) → O) → M) :
    ∑ o, f o = ∑ o' : Fin k → O, ∑ a : O, f (Fin.snoc o' a) := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => O)) (fun p => f (Fin.snocEquiv (fun _ => O) p)) f
    (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_comm]
  rfl

variable (W V : WildeQIT.Channel X O)

/-- Probability of an output prefix under channel `W`, given the local randomness. -/
noncomputable def pw (k : ℕ) (h : k ≤ n) (o : Fin k → O) : ℝ :=
  ∏ s : Fin k, (W (inp S ux uy k h s o)).prob (o s)

lemma pw_snoc (k : ℕ) (h : k + 1 ≤ n) (o' : Fin k → O) (a : O) :
    pw S ux uy W (k + 1) h (Fin.snoc o' a) =
      pw S ux uy W k (Nat.le_of_succ_le h) o' * (W (S.inputAt ⟨k, h⟩ ux uy o')).prob a := by
  unfold pw
  rw [Fin.prod_univ_castSucc]
  simp only [inp_snoc_castSucc, Fin.snoc_castSucc, inp_snoc_last, Fin.snoc_last]

lemma pw_nonneg (k : ℕ) (h : k ≤ n) (o : Fin k → O) : 0 ≤ pw S ux uy W k h o :=
  Finset.prod_nonneg fun s _ => (W _).nonneg _

lemma sum_pw : ∀ (k : ℕ) (h : k ≤ n), ∑ o : Fin k → O, pw S ux uy W k h o = 1 := by
  intro k
  induction k with
  | zero => intro h; simp [pw]
  | succ k ih =>
    intro h
    rw [sum_snoc]
    simp only [pw_snoc, ← Finset.mul_sum, (W _).sum_eq_one, mul_one]
    exact ih _

/-- Log-likelihood ratio and divergence (in bits). -/
noncomputable def Lr (x : X) (a : O) : ℝ := Real.logb 2 ((W x).prob a / (V x).prob a)

noncomputable def Dr (x : X) : ℝ := ∑ a, (W x).prob a * Lr W V x a

noncomputable def Zc (x : X) (a : O) : ℝ := Lr W V x a - Dr W V x

lemma sum_W_Zc (x : X) : ∑ a, (W x).prob a * Zc W V x a = 0 := by
  simp only [Zc, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (W x).sum_eq_one, one_mul]
  unfold Dr
  ring

/-- Total variance bound. -/
noncomputable def sig2 : ℝ := ∑ x, ∑ a, (W x).prob a * (Zc W V x a) ^ 2

lemma var_le (x : X) : ∑ a, (W x).prob a * (Zc W V x a) ^ 2 ≤ sig2 W V := by
  unfold sig2
  exact Finset.single_le_sum (f := fun x => ∑ a, (W x).prob a * (Zc W V x a) ^ 2)
    (fun x _ => Finset.sum_nonneg fun a _ => mul_nonneg ((W x).nonneg a) (sq_nonneg _))
    (Finset.mem_univ x)

/-- The centred log-likelihood martingale. -/
noncomputable def Mk (k : ℕ) (h : k ≤ n) (o : Fin k → O) : ℝ :=
  ∑ s : Fin k, Zc W V (inp S ux uy k h s o) (o s)

lemma Mk_snoc (k : ℕ) (h : k + 1 ≤ n) (o' : Fin k → O) (a : O) :
    Mk S ux uy W V (k + 1) h (Fin.snoc o' a) =
      Mk S ux uy W V k (Nat.le_of_succ_le h) o' + Zc W V (S.inputAt ⟨k, h⟩ ux uy o') a := by
  unfold Mk
  rw [Fin.sum_univ_castSucc]
  simp only [inp_snoc_castSucc, Fin.snoc_castSucc, inp_snoc_last, Fin.snoc_last]

/-- Second moment of the martingale: `E[M_k²] ≤ k σ²`. -/
lemma second_moment : ∀ (k : ℕ) (h : k ≤ n),
    ∑ o : Fin k → O, pw S ux uy W k h o * (Mk S ux uy W V k h o) ^ 2 ≤ k * sig2 W V := by
  intro k
  induction k with
  | zero => intro h; simp [Mk]
  | succ k ih =>
    intro h
    rw [sum_snoc]
    have hstep : ∀ o' : Fin k → O, ∑ a : O, pw S ux uy W (k + 1) h (Fin.snoc o' a) *
        (Mk S ux uy W V (k + 1) h (Fin.snoc o' a)) ^ 2 ≤
        pw S ux uy W k (Nat.le_of_succ_le h) o' * (Mk S ux uy W V k (Nat.le_of_succ_le h) o') ^ 2 +
          pw S ux uy W k (Nat.le_of_succ_le h) o' * sig2 W V := by
      intro o'
      set x := S.inputAt ⟨k, h⟩ ux uy o'
      set m := Mk S ux uy W V k (Nat.le_of_succ_le h) o'
      set q := pw S ux uy W k (Nat.le_of_succ_le h) o'
      have hq : 0 ≤ q := pw_nonneg S ux uy W k _ o'
      have hps := fun a => pw_snoc S ux uy W k h o' a
      have hms := fun a => Mk_snoc S ux uy W V k h o' a
      have hrw : ∀ a, pw S ux uy W (k + 1) h (Fin.snoc o' a) *
          (Mk S ux uy W V (k + 1) h (Fin.snoc o' a)) ^ 2 = q * (W x).prob a * (m + Zc W V x a) ^ 2 := by
        intro a; rw [hps a, hms a]
      rw [Finset.sum_congr rfl fun a _ => hrw a]
      have e : ∀ a, q * (W x).prob a * (m + Zc W V x a) ^ 2 =
          q * m ^ 2 * (W x).prob a + 2 * q * m * ((W x).prob a * Zc W V x a) +
            q * ((W x).prob a * (Zc W V x a) ^ 2) := fun a => by ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, (W x).sum_eq_one, sum_W_Zc,
        mul_one, mul_zero, add_zero]
      have := mul_le_mul_of_nonneg_left (var_le W V x) hq
      linarith
    calc ∑ o' : Fin k → O, ∑ a : O, pw S ux uy W (k + 1) h (Fin.snoc o' a) *
          (Mk S ux uy W V (k + 1) h (Fin.snoc o' a)) ^ 2
        ≤ ∑ o' : Fin k → O, (pw S ux uy W k (Nat.le_of_succ_le h) o' *
            (Mk S ux uy W V k (Nat.le_of_succ_le h) o') ^ 2 +
          pw S ux uy W k (Nat.le_of_succ_le h) o' * sig2 W V) := Finset.sum_le_sum fun o' _ => hstep o'
      _ = ∑ o' : Fin k → O, pw S ux uy W k (Nat.le_of_succ_le h) o' *
            (Mk S ux uy W V k (Nat.le_of_succ_le h) o') ^ 2 + sig2 W V := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_pw, one_mul]
      _ ≤ k * sig2 W V + sig2 W V := by linarith [ih (Nat.le_of_succ_le h)]
      _ = ((k + 1 : ℕ) : ℝ) * sig2 W V := by push_cast; ring

/-- Pointwise change of measure on one run. -/
lemma pw_le (hsupp : ∀ x a, (V x).prob a = 0 → (W x).prob a = 0) (Dm : ℝ)
    (hDm : ∀ x, Dr W V x ≤ Dm) (κ : ℝ) (o : Fin n → O) :
    pw S ux uy W n le_rfl o ≤ (2 : ℝ) ^ ((n : ℝ) * (Dm + κ)) * pw S ux uy V n le_rfl o +
      pw S ux uy W n le_rfl o * (if (n : ℝ) * κ < Mk S ux uy W V n le_rfl o then 1 else 0) := by
  have hpv : 0 ≤ pw S ux uy V n le_rfl o := pw_nonneg S ux uy V n le_rfl o
  have hpw : 0 ≤ pw S ux uy W n le_rfl o := pw_nonneg S ux uy W n le_rfl o
  split_ifs with hM
  · rw [mul_one]; nlinarith [Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) ((n : ℝ) * (Dm + κ))]
  rw [mul_zero, add_zero]
  rw [not_lt] at hM
  by_cases h0 : pw S ux uy W n le_rfl o = 0
  · rw [h0]; positivity
  -- every factor is positive
  have hW : ∀ s : Fin n, 0 < (W (inp S ux uy n le_rfl s o)).prob (o s) := by
    intro s
    refine lt_of_le_of_ne ((W _).nonneg _) (fun h => h0 ?_)
    exact Finset.prod_eq_zero (Finset.mem_univ s) h.symm
  have hV : ∀ s : Fin n, 0 < (V (inp S ux uy n le_rfl s o)).prob (o s) := by
    intro s
    refine lt_of_le_of_ne ((V _).nonneg _) (fun h => ?_)
    exact (hW s).ne' (hsupp _ _ h.symm)
  have hpvpos : 0 < pw S ux uy V n le_rfl o := Finset.prod_pos fun s _ => hV s
  have hpwpos : 0 < pw S ux uy W n le_rfl o := Finset.prod_pos fun s _ => hW s
  -- log-likelihood ratio
  have hlog : Real.logb 2 (pw S ux uy W n le_rfl o / pw S ux uy V n le_rfl o) =
      Mk S ux uy W V n le_rfl o + ∑ s : Fin n, Dr W V (inp S ux uy n le_rfl s o) := by
    unfold Mk pw
    rw [← Finset.prod_div_distrib, Real.logb_prod _ _ (fun s _ => (div_pos (hW s) (hV s)).ne'),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold Zc Lr
    ring
  have hD : ∑ s : Fin n, Dr W V (inp S ux uy n le_rfl s o) ≤ n * Dm := by
    calc ∑ s : Fin n, Dr W V (inp S ux uy n le_rfl s o) ≤ ∑ _s : Fin n, Dm :=
          Finset.sum_le_sum fun s _ => hDm _
      _ = n * Dm := by simp
  have hratio : pw S ux uy W n le_rfl o / pw S ux uy V n le_rfl o ≤
      (2 : ℝ) ^ ((n : ℝ) * (Dm + κ)) := by
    rw [← Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num) (div_pos hpwpos hpvpos)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [hlog]; nlinarith
  rw [div_le_iff₀ hpvpos] at hratio
  linarith

/-- Chebyshev's inequality for the centred log-likelihood. -/
lemma cheb (κ : ℝ) (hκ : 0 < κ) (hn : 0 < n) :
    ∑ o : Fin n → O, pw S ux uy W n le_rfl o *
      (if (n : ℝ) * κ < Mk S ux uy W V n le_rfl o then 1 else 0) ≤ sig2 W V / (n * κ ^ 2) := by
  have hnκ : 0 < (n : ℝ) * κ := mul_pos (by exact_mod_cast hn) hκ
  have hpt : ∀ o : Fin n → O, pw S ux uy W n le_rfl o *
      (if (n : ℝ) * κ < Mk S ux uy W V n le_rfl o then 1 else 0) ≤
      pw S ux uy W n le_rfl o * (Mk S ux uy W V n le_rfl o) ^ 2 / ((n : ℝ) * κ) ^ 2 := by
    intro o
    have hp := pw_nonneg S ux uy W n le_rfl o
    split_ifs with hM
    · rw [mul_one, mul_div_assoc]
      refine le_mul_of_one_le_right hp ?_
      rw [one_le_div (by positivity)]
      nlinarith
    · rw [mul_zero]; positivity
  calc _ ≤ ∑ o : Fin n → O, pw S ux uy W n le_rfl o * (Mk S ux uy W V n le_rfl o) ^ 2 /
        ((n : ℝ) * κ) ^ 2 := Finset.sum_le_sum fun o _ => hpt o
    _ = (∑ o : Fin n → O, pw S ux uy W n le_rfl o * (Mk S ux uy W V n le_rfl o) ^ 2) /
        ((n : ℝ) * κ) ^ 2 := by rw [Finset.sum_div]
    _ ≤ (n * sig2 W V) / ((n : ℝ) * κ) ^ 2 := by
        gcongr; exact second_moment S ux uy W V n le_rfl
    _ = sig2 W V / (n * κ ^ 2) := by
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp

end Prefix

section Integrate

/-- Product formula for the law of the first `k` outputs given the local randomness. -/
lemma go_apply (S : FeedbackStrategy X O n) (W : WildeQIT.Channel X O) (ux : S.Ux) (uy : S.Uy) :
    ∀ (k : ℕ) (h : k ≤ n) (o : Fin k → O),
      FeedbackStrategy.runLaw.go S W ux uy k h o =
        ∏ s : Fin k, ENNReal.ofReal ((W (S.inputAt ⟨s.val, lt_of_lt_of_le s.isLt h⟩ ux uy
          (fun i => o ⟨i.val, lt_trans i.isLt s.isLt⟩))).prob (o s)) := by
  intro k
  induction k with
  | zero =>
    intro h o
    simp only [FeedbackStrategy.runLaw.go, Finset.univ_eq_empty, Finset.prod_empty]
    rw [PMF.pure_apply, if_pos (funext fun i => Fin.elim0 i)]
  | succ k ih =>
    intro h o
    simp only [FeedbackStrategy.runLaw.go]
    rw [PMF.bind_apply, tsum_eq_single (Fin.init o)]
    · rw [PMF.map_apply, tsum_eq_single (o (Fin.last k))]
      · rw [if_pos (Fin.snoc_init_self o).symm, ih (Nat.le_of_succ_le h) (Fin.init o),
          Fin.prod_univ_castSucc]
        unfold finDistPMF
        rw [PMF.ofFintype_apply]
        rfl
      · intro y hy
        rw [if_neg]
        intro heq
        apply hy
        rw [heq, Fin.snoc_last]
    · intro o' ho'
      rw [PMF.map_apply]
      refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun y => ?_)
      rw [if_neg]
      intro heq
      apply ho'
      rw [heq, Fin.init_snoc]

lemma runLaw_apply (S : FeedbackStrategy X O n) (W : WildeQIT.Channel X O) (ux : S.Ux)
    (uy : S.Uy) (o : Fin n → O) :
    S.runLaw W (ux, uy, o) = S.lawX ux * S.lawY uy * FeedbackStrategy.runLaw.go S W ux uy n le_rfl o := by
  unfold FeedbackStrategy.runLaw
  rw [PMF.bind_apply, tsum_eq_single ux]
  · rw [PMF.bind_apply, tsum_eq_single uy]
    · rw [PMF.map_apply, tsum_eq_single o]
      · rw [if_pos rfl, mul_assoc]
      · intro o' ho'
        rw [if_neg]
        intro h; exact ho' (congrArg (fun t => t.2.2) h).symm
    · intro uy' huy'
      refine mul_eq_zero_of_right _ ?_
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.mpr fun o' => ?_
      rw [if_neg]
      intro h; exact huy' (congrArg (fun t => t.2.1) h).symm
  · intro ux' hux'
    refine mul_eq_zero_of_right _ ?_
    rw [PMF.bind_apply]
    refine ENNReal.tsum_eq_zero.mpr fun uy' => mul_eq_zero_of_right _ ?_
    rw [PMF.map_apply]
    refine ENNReal.tsum_eq_zero.mpr fun o' => ?_
    rw [if_neg]
    intro h; exact hux' (congrArg (fun t => t.1) h).symm


/-- `Σ' a, (p.map h) a * T a = Σ' c, p c * T (h c)`. -/
lemma tsum_map_mul {α β : Type} (p : PMF α) (h : α → β) (T : β → ℝ≥0∞) :
    ∑' b, (p.map h) b * T b = ∑' a, p a * T (h a) := by
  classical
  simp only [PMF.map_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (h a)]
  · simp
  · intro b hb; simp [hb]

/-- The observation of a run. -/
def obsFun (S : FeedbackStrategy X O n) (ux : S.Ux) (uy : S.Uy) (o : Fin n → O) :
    (Fin n → X) × (Fin n → O) × (Fin n → S.Fb) :=
  (fun s => S.inputAt s ux uy (fun i => o ⟨i, lt_trans i.isLt s.isLt⟩), o,
   fun s => S.feedback s (fun i => o ⟨i, lt_trans i.isLt s.isLt⟩) uy)

lemma obs_sum (S : FeedbackStrategy X O n) (W : WildeQIT.Channel X O)
    (T : (Fin n → X) × (Fin n → O) × (Fin n → S.Fb) → ℝ≥0∞) :
    ∑' b, (S.obsLaw W) b * T b = ∑' ux, ∑' uy, ∑ o : Fin n → O,
      S.lawX ux * S.lawY uy * ENNReal.ofReal (pw S ux uy W n le_rfl o) * T (obsFun S ux uy o) := by
  unfold FeedbackStrategy.obsLaw
  rw [tsum_map_mul, ENNReal.tsum_prod']
  refine tsum_congr fun ux => ?_
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun uy => ?_
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [runLaw_apply, go_apply]
  unfold pw
  rw [ENNReal.ofReal_prod_of_nonneg (fun s _ => (W _).nonneg _)]
  rfl

/-- Integrated change of measure: `P_W[T] ≤ 2^{n(D+κ)} Q_V[T] + σ²/(nκ²)` for every strategy. -/
lemma change_of_measure (S : FeedbackStrategy X O n) (W V : WildeQIT.Channel X O)
    (hsupp : ∀ x a, (V x).prob a = 0 → (W x).prob a = 0) (Dm : ℝ) (hDm : ∀ x, Dr W V x ≤ Dm)
    (κ : ℝ) (hκ : 0 < κ) (hn : 0 < n)
    (T : (Fin n → X) × (Fin n → O) × (Fin n → S.Fb) → ℝ≥0∞) (hT : ∀ b, T b ≤ 1) :
    ∑' b, (S.obsLaw W) b * T b ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * (Dm + κ))) * ∑' b, (S.obsLaw V) b * T b +
        ENNReal.ofReal (sig2 W V / (n * κ ^ 2)) := by
  rw [obs_sum, obs_sum]
  set K := ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * (Dm + κ))) with hK
  set c := ENNReal.ofReal (sig2 W V / (n * κ ^ 2)) with hc
  have hinner : ∀ (ux : S.Ux) (uy : S.Uy), ∑ o : Fin n → O,
      S.lawX ux * S.lawY uy * ENNReal.ofReal (pw S ux uy W n le_rfl o) * T (obsFun S ux uy o) ≤
      K * ∑ o : Fin n → O, S.lawX ux * S.lawY uy * ENNReal.ofReal (pw S ux uy V n le_rfl o) *
        T (obsFun S ux uy o) + S.lawX ux * S.lawY uy * c := by
    intro ux uy
    set ind : (Fin n → O) → ℝ := fun o =>
      if (n : ℝ) * κ < Mk S ux uy W V n le_rfl o then 1 else 0 with hind
    have hpt : ∀ o : Fin n → O, ENNReal.ofReal (pw S ux uy W n le_rfl o) * T (obsFun S ux uy o) ≤
        K * (ENNReal.ofReal (pw S ux uy V n le_rfl o) * T (obsFun S ux uy o)) +
          ENNReal.ofReal (pw S ux uy W n le_rfl o * ind o) := by
      intro o
      have hreal := pw_le S ux uy W V hsupp Dm hDm κ o
      have hpv := pw_nonneg S ux uy V n le_rfl o
      have hpw := pw_nonneg S ux uy W n le_rfl o
      have hind0 : 0 ≤ ind o := by simp only [hind]; split_ifs <;> norm_num
      have h1 : ENNReal.ofReal (pw S ux uy W n le_rfl o) ≤
          K * ENNReal.ofReal (pw S ux uy V n le_rfl o) +
            ENNReal.ofReal (pw S ux uy W n le_rfl o * ind o) := by
        rw [hK, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (mul_nonneg hpw hind0)]
        exact ENNReal.ofReal_le_ofReal hreal
      calc ENNReal.ofReal (pw S ux uy W n le_rfl o) * T (obsFun S ux uy o)
          ≤ (K * ENNReal.ofReal (pw S ux uy V n le_rfl o) +
              ENNReal.ofReal (pw S ux uy W n le_rfl o * ind o)) * T (obsFun S ux uy o) := by
            gcongr
        _ = K * (ENNReal.ofReal (pw S ux uy V n le_rfl o) * T (obsFun S ux uy o)) +
              ENNReal.ofReal (pw S ux uy W n le_rfl o * ind o) * T (obsFun S ux uy o) := by ring
        _ ≤ _ := by
            gcongr
            calc ENNReal.ofReal (pw S ux uy W n le_rfl o * ind o) * T (obsFun S ux uy o)
                ≤ ENNReal.ofReal (pw S ux uy W n le_rfl o * ind o) * 1 := by gcongr; exact hT _
              _ = _ := mul_one _
    have hsum := Finset.sum_le_sum fun o (_ : o ∈ Finset.univ) => hpt o
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have hcheb : ∑ o : Fin n → O, ENNReal.ofReal (pw S ux uy W n le_rfl o * ind o) ≤ c := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => mul_nonneg (pw_nonneg S ux uy W n le_rfl o)
        (by simp only [hind]; split_ifs <;> norm_num))]
      exact ENNReal.ofReal_le_ofReal (cheb S ux uy W V κ hκ hn)
    have hsum' : ∑ o : Fin n → O, ENNReal.ofReal (pw S ux uy W n le_rfl o) * T (obsFun S ux uy o) ≤
        K * ∑ o : Fin n → O, ENNReal.ofReal (pw S ux uy V n le_rfl o) * T (obsFun S ux uy o) + c :=
      hsum.trans (add_le_add le_rfl hcheb)
    have e1 : ∀ (P : (Fin n → O) → ℝ≥0∞), ∑ o : Fin n → O, S.lawX ux * S.lawY uy * P o *
        T (obsFun S ux uy o) = S.lawX ux * S.lawY uy * ∑ o : Fin n → O, P o * T (obsFun S ux uy o) := by
      intro P; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun o _ => by ring
    rw [e1, e1]
    calc S.lawX ux * S.lawY uy * ∑ o : Fin n → O, ENNReal.ofReal (pw S ux uy W n le_rfl o) *
          T (obsFun S ux uy o)
        ≤ S.lawX ux * S.lawY uy * (K * ∑ o : Fin n → O, ENNReal.ofReal (pw S ux uy V n le_rfl o) *
            T (obsFun S ux uy o) + c) := by gcongr
      _ = _ := by ring
  calc ∑' ux, ∑' uy, ∑ o : Fin n → O, S.lawX ux * S.lawY uy *
        ENNReal.ofReal (pw S ux uy W n le_rfl o) * T (obsFun S ux uy o)
      ≤ ∑' ux, ∑' uy, (K * ∑ o : Fin n → O, S.lawX ux * S.lawY uy *
          ENNReal.ofReal (pw S ux uy V n le_rfl o) * T (obsFun S ux uy o) +
          S.lawX ux * S.lawY uy * c) :=
        ENNReal.tsum_le_tsum fun ux => ENNReal.tsum_le_tsum fun uy => hinner ux uy
    _ = _ := by
        simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, PMF.tsum_coe,
          one_mul]

/-- Lower bound on the active type-II error. -/
lemma activeBeta_ge (W V : WildeQIT.Channel X O)
    (hsupp : ∀ x a, (V x).prob a = 0 → (W x).prob a = 0) (Dm : ℝ) (hDm : ∀ x, Dr W V x ≤ Dm)
    (κ : ℝ) (hκ : 0 < κ) (hn : 0 < n) (ε' : ℝ) :
    ENNReal.ofReal ((2 : ℝ) ^ (-((n : ℝ) * (Dm + κ)))) *
        (ENNReal.ofReal (1 - ε') - ENNReal.ofReal (sig2 W V / (n * κ ^ 2))) ≤
      activeBeta ε' W V n := by
  unfold activeBeta
  refine le_iInf fun S => ?_
  unfold testBeta
  refine le_iInf fun T => le_iInf fun hT => le_iInf fun hP => ?_
  have hcm := change_of_measure S W V hsupp Dm hDm κ hκ hn T hT
  set Pw := ∑' b, (S.obsLaw W) b * T b
  set Qv := ∑' b, (S.obsLaw V) b * T b
  set K := ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * (Dm + κ)))
  set c := ENNReal.ofReal (sig2 W V / (n * κ ^ 2))
  have h1 : ENNReal.ofReal (1 - ε') - c ≤ K * Qv := by
    rw [tsub_le_iff_right]
    exact hP.trans hcm
  have hinv : ENNReal.ofReal ((2 : ℝ) ^ (-((n : ℝ) * (Dm + κ)))) * K = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by norm_num), neg_add_cancel,
      Real.rpow_zero, ENNReal.ofReal_one]
  calc ENNReal.ofReal ((2 : ℝ) ^ (-((n : ℝ) * (Dm + κ)))) * (ENNReal.ofReal (1 - ε') - c)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((n : ℝ) * (Dm + κ)))) * (K * Qv) := by gcongr
    _ = Qv := by rw [← mul_assoc, hinv, one_mul]

/-- The converse bound on `−log₂ β`. -/
lemma negLog_activeBeta_le (W V : WildeQIT.Channel X O)
    (hsupp : ∀ x a, (V x).prob a = 0 → (W x).prob a = 0) (Dm : ℝ) (hDm : ∀ x, Dr W V x ≤ Dm)
    (κ : ℝ) (hκ : 0 < κ) (hn : 0 < n) (ε' : ℝ)
    (hpos : 0 < 1 - ε' - sig2 W V / (n * κ ^ 2)) :
    negLog2 (activeBeta ε' W V n) ≤
      (((n : ℝ) * (Dm + κ) - Real.logb 2 (1 - ε' - sig2 W V / (n * κ ^ 2)) : ℝ) : EReal) := by
  have hc : 0 ≤ sig2 W V / (n * κ ^ 2) := by
    unfold sig2
    refine div_nonneg (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun a _ =>
      mul_nonneg ((W x).nonneg a) (sq_nonneg _)) (by positivity)
  have hge := activeBeta_ge W V hsupp Dm hDm κ hκ hn ε'
  rw [← ENNReal.ofReal_sub _ hc, ← ENNReal.ofReal_mul (by positivity)] at hge
  set y := (2 : ℝ) ^ (-((n : ℝ) * (Dm + κ))) * (1 - ε' - sig2 W V / (n * κ ^ 2)) with hy
  have hypos : 0 < y := by positivity
  have hlog2 : (0 : EReal) ≤ (((Real.log 2)⁻¹ : ℝ) : EReal) := by
    exact_mod_cast (inv_nonneg.mpr (Real.log_nonneg (by norm_num)))
  calc negLog2 (activeBeta ε' W V n) ≤ negLog2 (ENNReal.ofReal y) := by
        unfold negLog2
        exact mul_le_mul_of_nonneg_right (EReal.neg_le_neg_iff.mpr (ENNReal.log_le_log hge)) hlog2
    _ = _ := by
        unfold negLog2
        rw [ENNReal.log_ofReal_of_pos hypos, ← EReal.coe_neg, ← EReal.coe_mul]
        congr 1
        rw [hy, Real.log_mul (by positivity) hpos.ne', Real.log_rpow (by norm_num), Real.logb]
        field_simp
        ring

end Integrate

section PointMass

open scoped Classical

/-- The point mass at `x`. -/
noncomputable def delta (x : X) : WildeQIT.FinDist X where
  prob x' := if x' = x then 1 else 0
  nonneg x' := by split_ifs <;> norm_num
  sum_eq_one := by simp

lemma condDiv_delta (W V : WildeQIT.Channel X O)
    (hsupp : ∀ x a, (V x).prob a = 0 → (W x).prob a = 0) (x : X) :
    condDiv W V (delta x) = ((Dr W V x : ℝ) : EReal) := by
  unfold condDiv WildeQIT.relEntropy
  rw [if_pos]
  · congr 1
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
    · unfold Dr Lr
      refine Finset.sum_congr rfl fun a _ => ?_
      show (if x = x then (1:ℝ) else 0) * (W x).prob a * Real.logb 2
        ((if x = x then (1:ℝ) else 0) * (W x).prob a / ((if x = x then (1:ℝ) else 0) * (V x).prob a)) = _
      simp
    · intro x' _ hx'
      refine Finset.sum_eq_zero fun a _ => ?_
      show (if x' = x then (1:ℝ) else 0) * (W x').prob a * _ = 0
      simp [hx']
    · simp
  · rintro ⟨x', a⟩ h
    simp only [Function.mem_support] at h ⊢
    show (if x' = x then (1:ℝ) else 0) * (V x').prob a ≠ 0
    have h' : (if x' = x then (1:ℝ) else 0) * (W x').prob a ≠ 0 := h
    by_cases hx : x' = x
    · simp only [hx, if_true, one_mul] at h' ⊢
      exact fun hv => h' (hsupp x a hv)
    · simp [hx] at h'

lemma condDiv_delta_top (W V : WildeQIT.Channel X O) (x : X) (a : O)
    (hV : (V x).prob a = 0) (hW : (W x).prob a ≠ 0) : condDiv W V (delta x) = ⊤ := by
  unfold condDiv WildeQIT.relEntropy
  rw [if_neg]
  intro hs
  have := hs (show (x, a) ∈ Function.support (jointLaw (delta x) W).prob by
    show (if x = x then (1:ℝ) else 0) * (W x).prob a ≠ 0
    simpa using hW)
  apply this
  show (if x = x then (1:ℝ) else 0) * (V x).prob a = 0
  simp [hV]

end PointMass

section Rate

variable {Y Z : Type} [Fintype Y] [Fintype Z]

lemma floor_ge_half (y : ℝ) (hy : 1 ≤ y) : y / 2 ≤ (⌊y⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one y
  have h2 : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast Nat.one_le_floor_iff y |>.mpr hy
  linarith

/-- Strong converse for a fixed degraded channel `V`, finite-divergence case. -/
lemma rate_le_Dm (W : WildeQIT.Channel X (Y × Z)) (V₂ : WildeQIT.Channel X Z)
    (V₁ : WildeQIT.Channel Z Y) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hεδ : ε + δ < 1) (R : ℝ)
    (hR : IsAchievableRate W ε δ R)
    (hsupp : ∀ x a, (degradedChannel V₂ V₁ x).prob a = 0 → (W x).prob a = 0)
    (Dm : ℝ) (hDm : ∀ x, Dr W (degradedChannel V₂ V₁) x ≤ Dm) : R ≤ Dm := by
  obtain ⟨hR0, hev⟩ := hR
  set V := degradedChannel V₂ V₁ with hVdef
  set η := (1 - ε - δ) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η < 1 - ε - δ := by rw [hη]; linarith
  refine le_of_forall_pos_le_add fun κ hκ => ?_
  set σ := sig2 W V with hσ
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun a _ =>
    mul_nonneg ((W x).nonneg a) (sq_nonneg _)
  set C := 2 * Real.logb 2 (1 / η) - Real.logb 2 (η / 2) + 1 with hC
  -- eventually `R ≤ Dm + κ + C/n`
  obtain ⟨n1, hn1⟩ : ∃ n1 : ℕ, 2 * σ / (η * κ ^ 2) < n1 := exists_nat_gt _
  have hevn : ∀ᶠ n : ℕ in Filter.atTop, R ≤ Dm + κ + C / n := by
    filter_upwards [hev, Filter.eventually_ge_atTop (max n1 1)] with n hcode hn
    obtain ⟨hNZ, c, hc⟩ := hcode
    have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hn)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hsmall : σ / (n * κ ^ 2) ≤ η / 2 := by
      have hn1' : (n1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
      rw [div_le_iff₀ (by positivity)]
      have := lt_of_lt_of_le hn1 hn1'
      rw [div_lt_iff₀ (by positivity)] at this
      nlinarith
    have hpos : 0 < 1 - (ε + δ + η) - σ / (n * κ ^ 2) := by rw [hη]; linarith
    have h1 := WiretapFeedback.logN_le_negLog_activeBeta W V V₂ V₁ (fun x y z => rfl) ε δ η
      hε hδ hεδ c hc hη0 hη1
    have h2 := negLog_activeBeta_le W V hsupp Dm hDm κ hκ hn0 (ε + δ + η) hpos
    have h3 : Real.logb 2 (⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ : ℕ) ≤
        (n : ℝ) * (Dm + κ) - Real.logb 2 (1 - (ε + δ + η) - σ / (n * κ ^ 2)) +
          2 * Real.logb 2 (1 / η) := by
      have := h1.trans (add_le_add h2 le_rfl)
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at this
      exact this
    have h4 : Real.logb 2 (η / 2) ≤ Real.logb 2 (1 - (ε + δ + η) - σ / (n * κ ^ 2)) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) (by rw [hη] at hsmall ⊢; linarith)
    have hy : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have h5 : (n : ℝ) * R - 1 ≤ Real.logb 2 (⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ : ℕ) := by
      have := floor_ge_half _ hy
      have hlb := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) this
      rw [Real.logb_div (by positivity) (by norm_num), Real.logb_rpow (by norm_num) (by norm_num),
        Real.logb_self_eq_one (by norm_num)] at hlb
      exact hlb
    have hfin : (n : ℝ) * R ≤ (n : ℝ) * (Dm + κ) + C := by rw [hC]; linarith
    rw [show Dm + κ + C / n = ((n : ℝ) * (Dm + κ) + C) / n by field_simp, le_div_iff₀ hnR]
    linarith
  have hlim : Filter.Tendsto (fun n : ℕ => Dm + κ + C / n) Filter.atTop (nhds (Dm + κ)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat C).const_add (Dm + κ)
    simpa using this
  exact ge_of_tendsto hlim hevn

/-- The rate is bounded by `sup_p D(W‖V|p)` for every degraded `V`. -/
lemma rate_le (W : WildeQIT.Channel X (Y × Z)) [Nonempty X] (V₂ : WildeQIT.Channel X Z)
    (V₁ : WildeQIT.Channel Z Y) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hεδ : ε + δ < 1) (R : ℝ)
    (hR : IsAchievableRate W ε δ R) :
    ((R : ℝ) : EReal) ≤ ⨆ p : WildeQIT.FinDist X, condDiv W (degradedChannel V₂ V₁) p := by
  by_cases hsupp : ∀ x a, (degradedChannel V₂ V₁ x).prob a = 0 → (W x).prob a = 0
  · obtain ⟨xm, -, hxm⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := X))
      (Dr W (degradedChannel V₂ V₁))
    have hDm : ∀ x, Dr W (degradedChannel V₂ V₁) x ≤ Dr W (degradedChannel V₂ V₁) xm := by
      intro x
      rw [← hxm]
      exact Finset.le_sup' _ (Finset.mem_univ x)
    have hR' := rate_le_Dm W V₂ V₁ ε δ hε hδ hεδ R hR hsupp _ hDm
    calc ((R : ℝ) : EReal) ≤ ((Dr W (degradedChannel V₂ V₁) xm : ℝ) : EReal) := by
          exact_mod_cast hR'
      _ = condDiv W (degradedChannel V₂ V₁) (delta xm) := (condDiv_delta W _ hsupp xm).symm
      _ ≤ _ := le_iSup (fun p => condDiv W (degradedChannel V₂ V₁) p) (delta xm)
  · simp only [not_forall] at hsupp
    obtain ⟨x, a, hV, hW⟩ := hsupp
    calc ((R : ℝ) : EReal) ≤ ⊤ := le_top
      _ = condDiv W (degradedChannel V₂ V₁) (delta x) := (condDiv_delta_top W _ x a hV hW).symm
      _ ≤ _ := le_iSup (fun p => condDiv W (degradedChannel V₂ V₁) p) (delta x)

/-- An achievable rate forces a nonempty input alphabet. -/
lemma nonempty_of_achievable (W : WildeQIT.Channel X (Y × Z)) (ε δ R : ℝ)
    (hR : IsAchievableRate W ε δ R) : Nonempty X := by
  obtain ⟨n, hcode, hn⟩ := (hR.2.and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨hNZ, c, -⟩ := hcode
  obtain ⟨u, -⟩ := c.lawX.support_nonempty
  obtain ⟨uy, -⟩ := c.lawY.support_nonempty
  have hs : 0 < n := hn
  exact ⟨c.encoder ⟨0, hs⟩ ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩ u
    (fun _ => c.feedback ⟨0, hs⟩ (fun i => Fin.elim0 i) uy)⟩

end Rate

end StrongConvAux

open StrongConvAux in
theorem solution {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (W : WildeQIT.Channel X (Y × Z)) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hεδ : ε + δ < 1) :
    WiretapFeedback.wiretapCapacity W ε δ ≤
      ⨆ p : WildeQIT.FinDist X,
        ((WildeQIT.condMutualInfo (WiretapFeedback.jointLaw p W) : ℝ) : EReal) := by
  unfold WiretapFeedback.wiretapCapacity
  refine sSup_le fun r hr => ?_
  obtain ⟨R, hR, rfl⟩ := hr
  have : Nonempty X := nonempty_of_achievable W ε δ R hR
  have hmm := WiretapFeedback.minimax_condDiv_eq_max_condMutualInfo W
  rw [← hmm.2.2.2, ← hmm.2.2.1, ← hmm.2.1, ← hmm.1]
  exact le_iInf₂ fun V₂ V₁ => rate_le W V₂ V₁ ε δ hε hδ hεδ R hR
