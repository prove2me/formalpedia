-- Prove2me | solution 1 for WiretapFeedback.activeStein
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T06:44:39.347118+00:00
-- url     : https://prove2.me/submissions/f652c95e-307d-4ffb-ac18-be97dc913fe6

import Mathlib
import Definitions.Def_WiretapFeedback_negLog2
import Definitions.Def_WiretapFeedback_activeBeta
import Definitions.Def_WiretapFeedback_condDiv

open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

section Stein

/-! ### Part (2): the supremum over input laws -/

open scoped Classical

lemma condDiv_eq_sum (W V : WildeQIT.Channel X O)
    (hsupp : ∀ x a, (V x).prob a = 0 → (W x).prob a = 0) (p : WildeQIT.FinDist X) :
    condDiv W V p = ((∑ x, p.prob x * Dr W V x : ℝ) : EReal) := by
  unfold condDiv WildeQIT.relEntropy
  rw [if_pos]
  · congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold Dr Lr
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    show p.prob x * (W x).prob a * Real.logb 2 (p.prob x * (W x).prob a / (p.prob x * (V x).prob a)) = _
    by_cases hp : p.prob x = 0
    · simp [hp]
    · rw [mul_div_mul_left _ _ hp]; ring
  · rintro ⟨x, a⟩ h
    simp only [Function.mem_support] at h ⊢
    show p.prob x * (V x).prob a ≠ 0
    have h' : p.prob x * (W x).prob a ≠ 0 := h
    intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h' (by rw [h1, zero_mul])
    · exact h' (by rw [hsupp x a h1, mul_zero])

lemma relEntropy_eq (W V : WildeQIT.Channel X O)
    (hsupp : ∀ x a, (V x).prob a = 0 → (W x).prob a = 0) (x : X) :
    WildeQIT.relEntropy (W x) (V x).prob = ((Dr W V x : ℝ) : EReal) := by
  unfold WildeQIT.relEntropy
  rw [if_pos]
  · rfl
  · intro a h
    simp only [Function.mem_support] at h ⊢
    exact fun hv => h (hsupp x a hv)

lemma relEntropy_top (W V : WildeQIT.Channel X O) (x : X) (a : O)
    (hV : (V x).prob a = 0) (hW : (W x).prob a ≠ 0) :
    WildeQIT.relEntropy (W x) (V x).prob = ⊤ := by
  unfold WildeQIT.relEntropy
  rw [if_neg]
  intro hs
  exact hs (show a ∈ Function.support (W x).prob from hW) hV

end Stein

section Const

/-- The non-adaptive strategy that always sends `x`. -/
noncomputable def constStrat (n : ℕ) (x : X) : FeedbackStrategy X O n where
  Fb := Unit
  Ux := Unit
  Uy := Unit
  lawX := PMF.pure ()
  lawY := PMF.pure ()
  feedback := fun _ _ _ => ()
  encoder := fun _ _ _ => x

/-- The (unique) local randomness values of `constStrat`. -/
def cu (n : ℕ) (x : X) : (constStrat (O := O) n x).Ux := ()

def cv (n : ℕ) (x : X) : (constStrat (O := O) n x).Uy := ()

lemma const_obs_sum (n : ℕ) (x : X) (P : WildeQIT.Channel X O)
    (u : (constStrat (O := O) n x).Ux) (v : (constStrat (O := O) n x).Uy)
    (T : (Fin n → X) × (Fin n → O) × (Fin n → (constStrat (O := O) n x).Fb) → ℝ≥0∞) :
    ∑' b, ((constStrat n x).obsLaw P) b * T b =
      ∑ o : Fin n → O, ENNReal.ofReal (∏ s, (P x).prob (o s)) *
        T (obsFun (constStrat n x) u v o) := by
  rw [obs_sum, tsum_eq_single u (fun b hb => (hb rfl).elim),
    tsum_eq_single v (fun b hb => (hb rfl).elim)]
  refine Finset.sum_congr rfl fun o _ => ?_
  have h1 : (constStrat (O := O) n x).lawX u = 1 := PMF.pure_apply_self _
  have h2 : (constStrat (O := O) n x).lawY v = 1 := PMF.pure_apply_self _
  rw [h1, h2, one_mul, one_mul]
  rfl

/-- If `supp W_{x₀} ⊄ supp V_{x₀}`, the type-II error is eventually zero. -/
lemma activeBeta_zero (W V : WildeQIT.Channel X O) (ε : ℝ) (hε0 : 0 < ε) (x0 : X) (a0 : O)
    (hV : (V x0).prob a0 = 0) (hW : (W x0).prob a0 ≠ 0) :
    ∀ᶠ n : ℕ in Filter.atTop, activeBeta ε W V n = 0 := by
  classical
  set w := (W x0).prob a0 with hw
  have hw0 : 0 < w := lt_of_le_of_ne ((W x0).nonneg a0) (Ne.symm hW)
  have hw1 : w ≤ 1 := WildeQIT.FinDist.prob_le_one _ _
  have hlim : Filter.Tendsto (fun n : ℕ => (1 - w) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  filter_upwards [hlim.eventually (gt_mem_nhds hε0)] with n hn
  refine le_antisymm ?_ zero_le
  refine (iInf_le _ (constStrat n x0)).trans ?_
  unfold testBeta
  let T : (Fin n → X) × (Fin n → O) × (Fin n → (constStrat (O := O) n x0).Fb) → ℝ≥0∞ :=
    fun b => if ∃ s, b.2.1 s = a0 then 1 else 0
  refine iInf_le_of_le T (iInf_le_of_le (fun b => by simp only [T]; split_ifs <;> simp) ?_)
  have hT : ∀ o, T (obsFun (constStrat n x0) (cu n x0) (cv n x0) o) =
      if ∃ s, o s = a0 then 1 else 0 := fun _ => rfl
  have hQ : ∑' b, ((constStrat n x0).obsLaw V) b * T b = 0 := by
    rw [const_obs_sum n x0 V (cu n x0) (cv n x0)]
    refine Finset.sum_eq_zero fun o _ => ?_
    rw [hT]
    split_ifs with h
    · obtain ⟨s, hs⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs, hV]), ENNReal.ofReal_zero, zero_mul]
    · rw [mul_zero]
  have hP : ENNReal.ofReal (1 - ε) ≤ ∑' b, ((constStrat n x0).obsLaw W) b * T b := by
    rw [const_obs_sum n x0 W (cu n x0) (cv n x0)]
    have hsplit : ∀ o : Fin n → O, ENNReal.ofReal (∏ s, (W x0).prob (o s)) *
        T (obsFun (constStrat n x0) (cu n x0) (cv n x0) o) =
          ENNReal.ofReal ((∏ s, (W x0).prob (o s)) -
            ∏ s, ((W x0).prob (o s) * if o s = a0 then 0 else 1)) := by
      intro o
      rw [hT]
      split_ifs with h
      · obtain ⟨s, hs⟩ := h
        have hz : ∏ s, ((W x0).prob (o s) * if o s = a0 then (0:ℝ) else 1) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])
        rw [hz, sub_zero, mul_one]
      · simp only [not_exists] at h
        simp [h]
    simp only [hsplit]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · apply ENNReal.ofReal_le_ofReal
      rw [Finset.sum_sub_distrib, ← Fintype.prod_sum (fun _ a => (W x0).prob a),
        ← Fintype.prod_sum (fun _ a => (W x0).prob a * if a = a0 then 0 else 1)]
      simp only [(W x0).sum_eq_one, Finset.prod_const_one, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      have hsp : ∀ a, (W x0).prob a * (if a = a0 then (0:ℝ) else 1) =
          (W x0).prob a - (if a = a0 then w else 0) := by
        intro a
        split_ifs with h
        · rw [h, mul_zero, sub_self]
        · rw [mul_one, sub_zero]
      have : ∑ a, (W x0).prob a * (if a = a0 then (0:ℝ) else 1) = 1 - w := by
        rw [Finset.sum_congr rfl fun a _ => hsp a, Finset.sum_sub_distrib, (W x0).sum_eq_one,
          Finset.sum_ite_eq']
        simp
      rw [this]
      linarith
    · intro o _
      rw [sub_nonneg]
      refine Finset.prod_le_prod (fun s _ => ?_) (fun s _ => ?_)
      · exact mul_nonneg ((W x0).nonneg _) (by split_ifs <;> norm_num)
      · split_ifs <;> simp [(W x0).nonneg]
  exact iInf_le_of_le hP (le_of_eq hQ)

/-- Lower-tail Chebyshev inequality for the centred log-likelihood. -/
lemma cheb_lower (S : FeedbackStrategy X O n) (ux : S.Ux) (uy : S.Uy) (W V : WildeQIT.Channel X O)
    (κ : ℝ) (hκ : 0 < κ) (hn : 0 < n) :
    ∑ o : Fin n → O, pw S ux uy W n le_rfl o *
      (if Mk S ux uy W V n le_rfl o < -((n : ℝ) * κ) then 1 else 0) ≤ sig2 W V / (n * κ ^ 2) := by
  have hnκ : 0 < (n : ℝ) * κ := mul_pos (by exact_mod_cast hn) hκ
  have hpt : ∀ o : Fin n → O, pw S ux uy W n le_rfl o *
      (if Mk S ux uy W V n le_rfl o < -((n : ℝ) * κ) then 1 else 0) ≤
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

/-- Achievability: the constant strategy with a likelihood-ratio test. -/
lemma activeBeta_le_const (W V : WildeQIT.Channel X O)
    (hsupp : ∀ x a, (V x).prob a = 0 → (W x).prob a = 0) (x : X) (κ : ℝ) (hκ : 0 < κ)
    (hn : 0 < n) (ε : ℝ) (hsmall : sig2 W V / (n * κ ^ 2) ≤ ε) :
    activeBeta ε W V n ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((n : ℝ) * (Dr W V x - κ)))) := by
  classical
  set t : ℝ := (2 : ℝ) ^ ((n : ℝ) * (Dr W V x - κ)) with ht
  have htpos : 0 < t := by positivity
  have htinv : (2 : ℝ) ^ (-((n : ℝ) * (Dr W V x - κ))) = t⁻¹ := by
    rw [ht, Real.rpow_neg (by norm_num)]
  rw [htinv]
  refine (iInf_le _ (constStrat (O := O) n x)).trans ?_
  unfold testBeta
  let T : (Fin n → X) × (Fin n → O) × (Fin n → (constStrat (O := O) n x).Fb) → ℝ≥0∞ :=
    fun b => if t * ∏ s, (V x).prob (b.2.1 s) ≤ ∏ s, (W x).prob (b.2.1 s) then 1 else 0
  refine iInf_le_of_le T (iInf_le_of_le (fun b => by simp only [T]; split_ifs <;> simp) ?_)
  have hTo : ∀ o, T (obsFun (constStrat n x) (cu n x) (cv n x) o) =
      if t * ∏ s, (V x).prob (o s) ≤ ∏ s, (W x).prob (o s) then 1 else 0 := fun _ => rfl
  have hWsum : ∑ o : Fin n → O, ∏ s, (W x).prob (o s) = 1 := by
    rw [← Fintype.prod_sum (fun _ a => (W x).prob a)]
    simp [(W x).sum_eq_one]
  have hQ : ∑' b, ((constStrat n x).obsLaw V) b * T b ≤ ENNReal.ofReal t⁻¹ := by
    rw [const_obs_sum n x V (cu n x) (cv n x)]
    calc ∑ o : Fin n → O, ENNReal.ofReal (∏ s, (V x).prob (o s)) *
          T (obsFun (constStrat n x) (cu n x) (cv n x) o)
        ≤ ∑ o : Fin n → O, ENNReal.ofReal (t⁻¹ * ∏ s, (W x).prob (o s)) := by
          refine Finset.sum_le_sum fun o _ => ?_
          rw [hTo]
          split_ifs with h
          · rw [mul_one]
            exact ENNReal.ofReal_le_ofReal ((le_inv_mul_iff₀ htpos).mpr h)
          · rw [mul_zero]; exact zero_le
      _ = ENNReal.ofReal (t⁻¹ * ∑ o : Fin n → O, ∏ s, (W x).prob (o s)) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => mul_nonneg (inv_nonneg.mpr htpos.le)
            (Finset.prod_nonneg fun s _ => (W x).nonneg _)), Finset.mul_sum]
      _ = ENNReal.ofReal t⁻¹ := by rw [hWsum, mul_one]
  have hP : ENNReal.ofReal (1 - ε) ≤ ∑' b, ((constStrat n x).obsLaw W) b * T b := by
    rw [const_obs_sum n x W (cu n x) (cv n x)]
    set Tr : (Fin n → O) → ℝ := fun o =>
      if t * ∏ s, (V x).prob (o s) ≤ ∏ s, (W x).prob (o s) then 1 else 0 with hTr
    have hTr0 : ∀ o, 0 ≤ Tr o := fun o => by simp only [hTr]; split_ifs <;> norm_num
    have hreal : ∀ o, ENNReal.ofReal (∏ s, (W x).prob (o s)) *
        T (obsFun (constStrat n x) (cu n x) (cv n x) o) =
        ENNReal.ofReal ((∏ s, (W x).prob (o s)) * Tr o) := by
      intro o; rw [hTo]; simp only [hTr]; split_ifs <;> simp
    rw [Finset.sum_congr rfl fun o _ => hreal o, ← ENNReal.ofReal_sum_of_nonneg (fun o _ =>
      mul_nonneg (Finset.prod_nonneg fun s _ => (W x).nonneg _) (hTr0 o))]
    apply ENNReal.ofReal_le_ofReal
    have hch := cheb_lower (constStrat (O := O) n x) (cu n x) (cv n x) W V κ hκ hn
    have hpwc : ∀ o, pw (constStrat (O := O) n x) (cu n x) (cv n x) W n le_rfl o =
        ∏ s, (W x).prob (o s) := fun _ => rfl
    have hMkc : ∀ o, Mk (constStrat (O := O) n x) (cu n x) (cv n x) W V n le_rfl o =
        ∑ s, Zc W V x (o s) := fun _ => rfl
    simp only [hpwc, hMkc] at hch
    have hpt : ∀ o, (∏ s, (W x).prob (o s)) * (1 - Tr o) ≤ (∏ s, (W x).prob (o s)) *
        (if ∑ s, Zc W V x (o s) < -((n : ℝ) * κ) then 1 else 0) := by
      intro o
      have hp0 : 0 ≤ ∏ s, (W x).prob (o s) := Finset.prod_nonneg fun s _ => (W x).nonneg _
      by_cases hc : t * ∏ s, (V x).prob (o s) ≤ ∏ s, (W x).prob (o s)
      · have : Tr o = 1 := by simp only [hTr]; rw [if_pos hc]
        rw [this, sub_self, mul_zero]
        exact mul_nonneg hp0 (by split_ifs <;> norm_num)
      · have : Tr o = 0 := by simp only [hTr]; rw [if_neg hc]
        rw [this, sub_zero, mul_one]
        by_cases h0 : ∏ s, (W x).prob (o s) = 0
        · rw [h0, zero_mul]
        have hW : ∀ s, 0 < (W x).prob (o s) := by
          intro s
          refine lt_of_le_of_ne ((W x).nonneg _) (fun h => h0 ?_)
          exact Finset.prod_eq_zero (Finset.mem_univ s) h.symm
        have hV : ∀ s, 0 < (V x).prob (o s) := by
          intro s
          refine lt_of_le_of_ne ((V x).nonneg _) (fun h => ?_)
          exact (hW s).ne' (hsupp _ _ h.symm)
        have hpv : 0 < ∏ s, (V x).prob (o s) := Finset.prod_pos fun s _ => hV s
        have hpw : 0 < ∏ s, (W x).prob (o s) := Finset.prod_pos fun s _ => hW s
        have hlog : Real.logb 2 ((∏ s, (W x).prob (o s)) / ∏ s, (V x).prob (o s)) =
            ∑ s, Zc W V x (o s) + n * Dr W V x := by
          rw [← Finset.prod_div_distrib,
            Real.logb_prod _ _ (fun s _ => (div_pos (hW s) (hV s)).ne')]
          have e : ∀ s, Real.logb 2 ((W x).prob (o s) / (V x).prob (o s)) =
              Zc W V x (o s) + Dr W V x := fun s => by unfold Zc Lr; ring
          rw [Finset.sum_congr rfl fun s _ => e s, Finset.sum_add_distrib]
          simp
        have hlt : Real.logb 2 ((∏ s, (W x).prob (o s)) / ∏ s, (V x).prob (o s)) <
            (n : ℝ) * (Dr W V x - κ) := by
          rw [Real.logb_lt_iff_lt_rpow (by norm_num) (div_pos hpw hpv), div_lt_iff₀ hpv, ← ht]
          linarith [not_le.mp hc]
        rw [hlog] at hlt
        rw [if_pos (by linarith), mul_one]
    have hsum1 := Finset.sum_le_sum fun o (_ : o ∈ Finset.univ) => hpt o
    have hexp : ∑ o : Fin n → O, (∏ s, (W x).prob (o s)) * Tr o =
        ∑ o : Fin n → O, (∏ s, (W x).prob (o s)) -
          ∑ o : Fin n → O, (∏ s, (W x).prob (o s)) * (1 - Tr o) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun o _ => by ring
    rw [hexp, hWsum]
    linarith
  exact iInf_le_of_le hP hQ

end Const

section NegLog

lemma negLog2_anti {a b : ℝ≥0∞} (h : a ≤ b) : negLog2 b ≤ negLog2 a := by
  unfold negLog2
  have hlog2 : (0 : EReal) ≤ (((Real.log 2)⁻¹ : ℝ) : EReal) := by
    exact_mod_cast (inv_nonneg.mpr (Real.log_nonneg (by norm_num)))
  exact mul_le_mul_of_nonneg_right (EReal.neg_le_neg_iff.mpr (ENNReal.log_le_log h)) hlog2

lemma negLog2_rpow (y : ℝ) : negLog2 (ENNReal.ofReal ((2 : ℝ) ^ y)) = ((-y : ℝ) : EReal) := by
  unfold negLog2
  rw [ENNReal.log_ofReal_of_pos (by positivity), ← EReal.coe_neg, ← EReal.coe_mul]
  congr 1
  rw [Real.log_rpow (by norm_num)]
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp

lemma negLog2_zero : negLog2 0 = ⊤ := by
  unfold negLog2
  rw [ENNReal.log_zero, EReal.neg_bot, EReal.top_mul_of_pos]
  exact_mod_cast (inv_pos.mpr (Real.log_pos one_lt_two))

lemma negLog2_top : negLog2 ⊤ = ⊥ := by
  unfold negLog2
  rw [ENNReal.log_top, EReal.neg_top, EReal.bot_mul_of_pos]
  exact_mod_cast (inv_pos.mpr (Real.log_pos one_lt_two))

end NegLog

section Limits

open Filter Topology

lemma upper_eventually (W V : WildeQIT.Channel X O)
    (hsupp : ∀ x a, (V x).prob a = 0 → (W x).prob a = 0) (Dm : ℝ) (hDm : ∀ x, Dr W V x ≤ Dm)
    (ε : ℝ) (hε1 : ε < 1) (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, ((1 / n : ℝ) : EReal) * negLog2 (activeBeta ε W V n) ≤
      ((Dm + 2 * κ : ℝ) : EReal) := by
  set σ := sig2 W V with hσdef
  have hσ0 : 0 ≤ σ := by
    rw [hσdef]; unfold sig2
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun a _ =>
      mul_nonneg ((W x).nonneg a) (sq_nonneg _)
  set δ := 1 - ε with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set L := -Real.logb 2 (δ / 2) with hL
  have h1 : ∀ᶠ n : ℕ in atTop, σ / κ ^ 2 / n < δ / 2 :=
    (tendsto_const_div_atTop_nhds_zero_nat (σ / κ ^ 2)).eventually (gt_mem_nhds (by positivity))
  have h2 : ∀ᶠ n : ℕ in atTop, L / n < κ :=
    (tendsto_const_div_atTop_nhds_zero_nat L).eventually (gt_mem_nhds hκ)
  filter_upwards [h1, h2, eventually_gt_atTop 0] with n hn1 hn2 hn3
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn3
  have hσn : σ / (n * κ ^ 2) = σ / κ ^ 2 / n := by
    rw [div_div, mul_comm]
  have hpos : 0 < 1 - ε - σ / (n * κ ^ 2) := by rw [hσn]; linarith
  have hb := negLog_activeBeta_le W V hsupp Dm hDm κ hκ hn3 ε hpos
  have hlog : -Real.logb 2 (1 - ε - σ / (n * κ ^ 2)) ≤ L := by
    rw [hL]
    apply neg_le_neg
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    rw [hσn]; linarith
  have hnn : (0 : EReal) ≤ ((1 / n : ℝ) : EReal) := by
    exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / n)
  calc ((1 / n : ℝ) : EReal) * negLog2 (activeBeta ε W V n)
      ≤ ((1 / n : ℝ) : EReal) *
          (((n : ℝ) * (Dm + κ) - Real.logb 2 (1 - ε - σ / (n * κ ^ 2)) : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left hb hnn
    _ = (((1 / n) * ((n : ℝ) * (Dm + κ) - Real.logb 2 (1 - ε - σ / (n * κ ^ 2))) : ℝ) :
          EReal) := by rw [EReal.coe_mul]
    _ ≤ ((Dm + 2 * κ : ℝ) : EReal) := by
        rw [EReal.coe_le_coe_iff]
        have e : (1 / n) * ((n : ℝ) * (Dm + κ) - Real.logb 2 (1 - ε - σ / (n * κ ^ 2))) =
            Dm + κ + (-Real.logb 2 (1 - ε - σ / (n * κ ^ 2))) / n := by
          field_simp
          ring
        rw [e]
        have : (-Real.logb 2 (1 - ε - σ / (n * κ ^ 2))) / n ≤ L / n :=
          div_le_div_of_nonneg_right hlog hnr.le
        linarith

lemma lower_eventually (W V : WildeQIT.Channel X O)
    (hsupp : ∀ x a, (V x).prob a = 0 → (W x).prob a = 0) (x : X) (ε : ℝ) (hε0 : 0 < ε)
    (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, ((Dr W V x - κ : ℝ) : EReal) ≤
      ((1 / n : ℝ) : EReal) * negLog2 (activeBeta ε W V n) := by
  have h1 : ∀ᶠ n : ℕ in atTop, sig2 W V / κ ^ 2 / n < ε :=
    (tendsto_const_div_atTop_nhds_zero_nat _).eventually (gt_mem_nhds hε0)
  filter_upwards [h1, eventually_gt_atTop 0] with n hn1 hn2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn2
  have hsmall : sig2 W V / (n * κ ^ 2) ≤ ε := by
    rw [div_div, mul_comm] at hn1; exact hn1.le
  have hb := activeBeta_le_const W V hsupp x κ hκ hn2 ε hsmall
  have hneg := negLog2_anti hb
  rw [negLog2_rpow, neg_neg] at hneg
  have hnn : (0 : EReal) ≤ ((1 / n : ℝ) : EReal) := by
    exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / n)
  calc ((Dr W V x - κ : ℝ) : EReal)
      = ((1 / n : ℝ) : EReal) * (((n : ℝ) * (Dr W V x - κ) : ℝ) : EReal) := by
        rw [← EReal.coe_mul]; congr 1; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hneg hnn

end Limits

end StrongConvAux

open Filter Topology StrongConvAux WiretapFeedback in
/-- **Theorem 4** (adaptive Stein lemma, Hayashi 2009; Hayashi–Tyagi–Watanabe arXiv:1410.0443v1). -/
theorem solution {X O : Type} [Fintype X] [Fintype O] (W V : WildeQIT.Channel X O) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => (((1 : ℝ) / n : ℝ) : EReal) *
        WiretapFeedback.negLog2 (WiretapFeedback.activeBeta ε W V n)) atTop
        (𝓝 (⨆ p : WildeQIT.FinDist X, WiretapFeedback.condDiv W V p)) ∧
      (⨆ p : WildeQIT.FinDist X, WiretapFeedback.condDiv W V p) =
        ⨆ x : X, WildeQIT.relEntropy (W x) (V x).prob := by
  classical
  by_cases hX : IsEmpty X
  · -- no inputs: both sides are `⊥`, and there is no strategy of positive length
    have : IsEmpty (WildeQIT.FinDist X) := ⟨fun p => by have := p.sum_eq_one; simp at this⟩
    have hS : (⨆ p : WildeQIT.FinDist X, condDiv W V p) = ⊥ := iSup_of_empty _
    have hR : (⨆ x : X, WildeQIT.relEntropy (W x) (V x).prob) = ⊥ := iSup_of_empty _
    refine ⟨?_, hS.trans hR.symm⟩
    rw [hS]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : IsEmpty (FeedbackStrategy X O n) := ⟨fun S => by
      obtain ⟨ux, -⟩ := S.lawX.support_nonempty
      obtain ⟨uy, -⟩ := S.lawY.support_nonempty
      exact hX.elim (S.encoder ⟨0, hn⟩ ux (fun _ => S.feedback ⟨0, hn⟩ (fun i => i.elim0) uy))⟩
    have hβ : activeBeta ε W V n = ⊤ := iInf_of_empty _
    have hpos : (0 : EReal) < (((1 : ℝ) / n : ℝ) : EReal) := by
      exact_mod_cast (by positivity : (0 : ℝ) < 1 / n)
    show (⊥ : EReal) = _
    rw [hβ, negLog2_top, EReal.mul_bot_of_pos hpos]
  rw [not_isEmpty_iff] at hX
  by_cases hs : ∀ x a, (V x).prob a = 0 → (W x).prob a = 0
  · -- finite case
    obtain ⟨xs, hxs⟩ := Finite.exists_max (Dr W V)
    set Dm := Dr W V xs with hDm
    have hS : (⨆ p : WildeQIT.FinDist X, condDiv W V p) = ((Dm : ℝ) : EReal) := by
      apply le_antisymm
      · refine iSup_le fun p => ?_
        rw [condDiv_eq_sum W V hs p]
        refine EReal.coe_le_coe_iff.mpr ?_
        calc ∑ x, p.prob x * Dr W V x ≤ ∑ x, p.prob x * Dm :=
              Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hxs x) (p.nonneg x)
          _ = Dm := by rw [← Finset.sum_mul, p.sum_eq_one, one_mul]
      · rw [← condDiv_delta W V hs xs]
        exact le_iSup (fun p => condDiv W V p) (delta xs)
    have hR : (⨆ x : X, WildeQIT.relEntropy (W x) (V x).prob) = ((Dm : ℝ) : EReal) := by
      apply le_antisymm
      · refine iSup_le fun x => ?_
        rw [relEntropy_eq W V hs x]
        exact EReal.coe_le_coe_iff.mpr (hxs x)
      · rw [← relEntropy_eq W V hs xs]
        exact le_iSup (fun x => WildeQIT.relEntropy (W x) (V x).prob) xs
    refine ⟨?_, hS.trans hR.symm⟩
    rw [hS]
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨r, har, hr⟩ := EReal.lt_iff_exists_real_btwn.mp ha
      have hr' : r < Dm := EReal.coe_lt_coe_iff.mp hr
      have hκ : 0 < (Dm - r) / 2 := by linarith
      filter_upwards [lower_eventually W V hs xs ε hε0 _ hκ] with n hn
      refine lt_of_lt_of_le har (le_trans ?_ hn)
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    · obtain ⟨r, hr, har⟩ := EReal.lt_iff_exists_real_btwn.mp ha
      have hr' : Dm < r := EReal.coe_lt_coe_iff.mp hr
      have hκ : 0 < (r - Dm) / 3 := by linarith
      filter_upwards [upper_eventually W V hs Dm hxs ε hε1 _ hκ] with n hn
      refine lt_of_le_of_lt hn (lt_trans ?_ har)
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
  · -- infinite case
    simp only [not_forall] at hs
    obtain ⟨x0, a0, hV0, hW0⟩ := hs
    have hS : (⨆ p : WildeQIT.FinDist X, condDiv W V p) = ⊤ := by
      refine eq_top_iff.mpr ?_
      rw [← condDiv_delta_top W V x0 a0 hV0 hW0]
      exact le_iSup (fun p => condDiv W V p) (delta x0)
    have hR : (⨆ x : X, WildeQIT.relEntropy (W x) (V x).prob) = ⊤ := by
      refine eq_top_iff.mpr ?_
      rw [← relEntropy_top W V x0 a0 hV0 hW0]
      exact le_iSup (fun x => WildeQIT.relEntropy (W x) (V x).prob) x0
    refine ⟨?_, hS.trans hR.symm⟩
    rw [hS]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [activeBeta_zero W V ε hε0 x0 a0 hV0 hW0, eventually_gt_atTop 0] with n hn hn'
    have hpos : (0 : EReal) < (((1 : ℝ) / n : ℝ) : EReal) := by
      exact_mod_cast (by positivity : (0 : ℝ) < 1 / n)
    show (⊤ : EReal) = _
    rw [hn, negLog2_zero, EReal.mul_top_of_pos hpos]
