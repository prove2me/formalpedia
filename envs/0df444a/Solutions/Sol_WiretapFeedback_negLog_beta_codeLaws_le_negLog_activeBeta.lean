-- Prove2me | solution 1 for WiretapFeedback.negLog_beta_codeLaws_le_negLog_activeBeta
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T05:50:32.795352+00:00
-- url     : https://prove2.me/submissions/6469942d-1dd1-4b3c-a7f1-715ad8c2203b

import Mathlib
import Definitions.Def_WiretapFeedback_negLog2
import Definitions.Def_WiretapFeedback_testBeta
import Definitions.Def_WiretapFeedback_activeBeta
import Definitions.Def_WiretapFeedback_WiretapCode_law

open scoped ENNReal

namespace WiretapAux

open WiretapFeedback

variable {X O : Type} [Fintype O] {n : ℕ}

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

section Code

variable {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ}

lemma toStrategy_lawX (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (m : Fin N) (u : c.Ux) :
    (c.toStrategy Z μ).lawX (m, u) = μ m * c.lawX u := by
  show (μ.bind fun m => c.lawX.map fun u => (m, u)) (m, u) = _
  rw [PMF.bind_apply, tsum_eq_single m]
  · rw [PMF.map_apply, tsum_eq_single u]
    · simp
    · intro u' hu'
      rw [if_neg]
      intro h; exact hu' (congrArg Prod.snd h).symm
  · intro m' hm'
    refine mul_eq_zero_of_right _ ?_
    rw [PMF.map_apply]
    exact ENNReal.tsum_eq_zero.mpr fun u' => if_neg (fun h => hm' (congrArg Prod.fst h).symm)

/-- The feedback sequence produced from Bob's outputs `y` and his randomness. -/
def Fseq (c : WiretapCode X Y N n) (y : Fin n → Y) (uy : c.Uy) : Fin n → c.Fb :=
  fun s => c.feedback s (fun i => y ⟨i, lt_trans i.isLt s.isLt⟩) uy

end Code

end WiretapAux

namespace ActiveAux

open WiretapFeedback WiretapAux

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

/-- Marginal on the second coordinate. -/
lemma map_snd_apply {A B : Type} (P : PMF (A × B)) (b : B) :
    (P.map Prod.snd) b = ∑' a, P (a, b) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single b]
  · simp
  · intro b' hb'; rw [if_neg]; intro h; exact hb' h.symm

section Joint

variable {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ}

/-- The observation `(Xⁿ, Oⁿ, 𝐅)` of a run of the code strategy. -/
noncomputable def obsOf (c : WiretapCode X Y N n) (μ : PMF (Fin N))
    (r : (c.toStrategy Z μ).Ux × (c.toStrategy Z μ).Uy × (Fin n → Y × Z)) :
    (Fin n → X) × (Fin n → Y × Z) × (Fin n → c.Fb) :=
  (fun s => (c.toStrategy Z μ).inputAt s r.1 r.2.1 (fun i => r.2.2 ⟨i, lt_trans i.isLt s.isLt⟩),
   r.2.2,
   fun s => (c.toStrategy Z μ).feedback s (fun i => r.2.2 ⟨i, lt_trans i.isLt s.isLt⟩) r.2.1)

/-- Joint law of the message and the observation. -/
noncomputable def JW (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (W : WildeQIT.Channel X (Y × Z)) :
    PMF (Fin N × ((Fin n → X) × (Fin n → Y × Z) × (Fin n → c.Fb))) :=
  ((c.toStrategy Z μ).runLaw W).map fun r => ((r.1 : Fin N × c.Ux).1, obsOf c μ r)

lemma obsLaw_eq (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (W : WildeQIT.Channel X (Y × Z)) :
    (c.toStrategy Z μ).obsLaw W = (JW c μ W).map Prod.snd := by
  unfold JW FeedbackStrategy.obsLaw
  rw [PMF.map_comp]
  rfl

/-- The decoded code law as a function of the message and the observation. -/
def lawFun (c : WiretapCode X Y N n)
    (p : Fin N × ((Fin n → X) × (Fin n → Y × Z) × (Fin n → c.Fb))) :
    Fin N × Fin N × (Fin n → Z) × (Fin n → c.Fb) :=
  (p.1, c.decoder (fun s => (p.2.2.1 s).1), (fun s => (p.2.2.1 s).2), p.2.2.2)

lemma law_eq (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (W : WildeQIT.Channel X (Y × Z)) :
    c.law μ W = (JW c μ W).map (lawFun c) := by
  unfold JW WiretapCode.law
  rw [PMF.map_comp]
  rfl

open scoped Classical in
/-- Transmitter factor. -/
noncomputable def Afun (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (m : Fin N)
    (x : Fin n → X) (f : Fin n → c.Fb) : ℝ≥0∞ :=
  μ m * ∑' u, c.lawX u * (if x = fun s => c.encoder s m u
    (fun r => f ⟨r.val, lt_of_lt_of_le r.isLt (Nat.succ_le_of_lt s.isLt)⟩) then 1 else 0)

open scoped Classical in
/-- Receiver factor. -/
noncomputable def Bfun (c : WiretapCode X Y N n) (o : Fin n → Y × Z) (f : Fin n → c.Fb) : ℝ≥0∞ :=
  ∑' uy, c.lawY uy * (if f = Fseq c (fun s => (o s).1) uy then 1 else 0)

/-- Channel factor. -/
noncomputable def Cfun (W : WildeQIT.Channel X (Y × Z)) (x : Fin n → X) (o : Fin n → Y × Z) :
    ℝ≥0∞ :=
  ∏ s, ENNReal.ofReal ((W (x s)).prob (o s))

lemma JW_apply (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (W : WildeQIT.Channel X (Y × Z))
    (m : Fin N) (x : Fin n → X) (o : Fin n → Y × Z) (f : Fin n → c.Fb) :
    JW c μ W (m, x, o, f) = Afun c μ m x f * (Bfun c o f * Cfun W x o) := by
  classical
  unfold JW
  rw [PMF.map_apply]
  have hsplit : ∀ F : (Fin N × c.Ux) × c.Uy × (Fin n → Y × Z) → ℝ≥0∞,
      ∑' a, F a = ∑' (m0 : Fin N) (u : c.Ux) (uy : c.Uy) (o : Fin n → Y × Z), F ((m0, u), uy, o) := by
    intro F
    rw [ENNReal.tsum_prod', ENNReal.tsum_prod']
    refine tsum_congr fun m0 => ?_
    refine tsum_congr fun u => ?_
    rw [ENNReal.tsum_prod']
  refine (hsplit _).trans ?_
  rw [tsum_eq_single m]
  swap
  · intro m0 hm0
    refine ENNReal.tsum_eq_zero.mpr fun u => ENNReal.tsum_eq_zero.mpr fun uy =>
      ENNReal.tsum_eq_zero.mpr fun o' => ?_
    rw [if_neg]
    intro h
    exact hm0 (congrArg Prod.fst h).symm
  have hterm : ∀ (u : c.Ux) (uy : c.Uy), (∑' o' : Fin n → Y × Z,
      @ite _ ((m, x, o, f) = (((m, u), uy, o').1.1, obsOf c μ ((m, u), uy, o')))
        (Classical.propDecidable _)
        (((WiretapCode.toStrategy Z c μ).runLaw W) ((m, u), uy, o')) 0) =
      (μ m * (c.lawX u * (if x = fun s => c.encoder s m u
        (fun r => f ⟨r.val, lt_of_lt_of_le r.isLt (Nat.succ_le_of_lt s.isLt)⟩) then 1 else 0))) *
      ((c.lawY uy * (if f = Fseq c (fun s => (o s).1) uy then 1 else 0)) * Cfun W x o) := by
    intro u uy
    rw [tsum_eq_single o]
    swap
    · intro o' ho'
      rw [if_neg]
      intro h
      exact ho' (congrArg (fun t => t.2.2.1) h).symm
    have hobs : obsOf c μ ((m, u), uy, o) = ((fun s => c.encoder s m u
        (fun r => Fseq c (fun s => (o s).1) uy ⟨r.val, lt_of_lt_of_le r.isLt
          (Nat.succ_le_of_lt s.isLt)⟩)), o, Fseq c (fun s => (o s).1) uy) := rfl
    by_cases hf : f = Fseq c (fun s => (o s).1) uy
    · by_cases hx : x = fun s => c.encoder s m u
          (fun r => f ⟨r.val, lt_of_lt_of_le r.isLt (Nat.succ_le_of_lt s.isLt)⟩)
      · rw [if_pos, if_pos hx, if_pos hf]
        swap
        · simp only
          rw [hobs, ← hf, ← hx]
        erw [runLaw_apply]
        rw [toStrategy_lawX]
        erw [go_apply]
        have hY : (WiretapCode.toStrategy Z c μ).lawY uy = c.lawY uy := rfl
        erw [hY]
        have hC : (∏ s : Fin n, ENNReal.ofReal ((W ((WiretapCode.toStrategy Z c μ).inputAt
            ⟨s.val, lt_of_lt_of_le s.isLt le_rfl⟩ (m, u) uy
            (fun i => o ⟨i.val, lt_trans i.isLt s.isLt⟩))).prob (o s))) = Cfun W x o := by
          unfold Cfun
          refine Finset.prod_congr rfl fun s _ => ?_
          rw [hx, hf]
          rfl
        erw [hC]
        ring
      · rw [if_neg, if_neg hx]
        · ring
        · simp only
          rw [hobs, ← hf]
          intro h
          exact hx (congrArg (fun t => t.2.1) h)
    · rw [if_neg, if_neg hf]
      · ring
      · simp only
        rw [hobs]
        intro h
        exact hf (congrArg (fun t => t.2.2.2) h)
  refine (tsum_congr fun u => tsum_congr fun uy => hterm u uy).trans ?_
  unfold Afun Bfun
  simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]
  ring

end Joint

section Main

variable {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ}

/-- The randomized active test that simulates a test on the code law (posterior average). -/
noncomputable def simTest (c : WiretapCode X Y N n) (μ : PMF (Fin N))
    (T : Fin N × Fin N × (Fin n → Z) × (Fin n → c.Fb) → ℝ≥0∞)
    (b : (Fin n → X) × (Fin n → Y × Z) × (Fin n → c.Fb)) : ℝ≥0∞ :=
  (∑' m, Afun c μ m b.1 b.2.2 * T (lawFun c (m, b))) / ∑' m, Afun c μ m b.1 b.2.2

lemma Afun_sum_le (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (x : Fin n → X)
    (f : Fin n → c.Fb) : ∑' m, Afun c μ m x f ≤ 1 := by
  classical
  calc ∑' m, Afun c μ m x f ≤ ∑' m, μ m * 1 := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        unfold Afun
        gcongr
        calc ∑' u, c.lawX u * (if x = fun s => c.encoder s m u
              (fun r => f ⟨r.val, lt_of_lt_of_le r.isLt (Nat.succ_le_of_lt s.isLt)⟩) then 1 else 0)
            ≤ ∑' u, c.lawX u := ENNReal.tsum_le_tsum fun u => by
              split_ifs <;> simp
          _ = 1 := c.lawX.tsum_coe
    _ = 1 := by simp only [mul_one]; exact μ.tsum_coe

lemma simTest_le_one (c : WiretapCode X Y N n) (μ : PMF (Fin N))
    (T : Fin N × Fin N × (Fin n → Z) × (Fin n → c.Fb) → ℝ≥0∞) (hT : ∀ a, T a ≤ 1)
    (b : (Fin n → X) × (Fin n → Y × Z) × (Fin n → c.Fb)) : simTest c μ T b ≤ 1 := by
  unfold simTest
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact ENNReal.tsum_le_tsum fun m => mul_le_of_le_one_right' (hT _)

lemma obs_eq_law (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (W : WildeQIT.Channel X (Y × Z))
    (T : Fin N × Fin N × (Fin n → Z) × (Fin n → c.Fb) → ℝ≥0∞) (hT : ∀ a, T a ≤ 1) :
    ∑' b, ((c.toStrategy Z μ).obsLaw W) b * simTest c μ T b = ∑' a, (c.law μ W) a * T a := by
  have e1 : ∑' b, ((c.toStrategy Z μ).obsLaw W) b * simTest c μ T b =
      ∑' p, JW c μ W p * simTest c μ T p.2 := by
    have := tsum_map_mul (JW c μ W) Prod.snd (simTest c μ T)
    rw [← obsLaw_eq] at this
    exact this
  rw [e1, law_eq, tsum_map_mul, ENNReal.tsum_prod', ENNReal.tsum_prod',
    ENNReal.tsum_comm, ENNReal.tsum_comm (f := fun m b => JW c μ W (m, b) * T (lawFun c (m, b)))]
  refine tsum_congr fun b => ?_
  obtain ⟨x, o, f⟩ := b
  simp only [JW_apply]
  set A := fun m => Afun c μ m x f
  set K := Bfun c o f * Cfun W x o
  have hL : ∑' m, A m * K * simTest c μ T (x, o, f) =
      K * ((∑' m, A m) * ((∑' m, A m * T (lawFun c (m, (x, o, f)))) / ∑' m, A m)) := by
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    unfold simTest
    ring
  have hR : ∑' m, A m * K * T (lawFun c (m, (x, o, f))) =
      K * ∑' m, A m * T (lawFun c (m, (x, o, f))) := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun m => ?_
    ring
  rw [hL, hR]
  congr 1
  by_cases h0 : ∑' m, A m = 0
  · rw [h0, zero_mul]
    have : ∀ m, A m = 0 := fun m => (ENNReal.tsum_eq_zero.mp h0) m
    symm
    exact ENNReal.tsum_eq_zero.mpr fun m => by rw [this m, zero_mul]
  · exact ENNReal.mul_div_cancel h0 (ne_top_of_le_ne_top ENNReal.one_ne_top (Afun_sum_le c μ x f))

end Main

end ActiveAux

open ActiveAux in
theorem solution {X Y Z : Type} [Fintype Y] [Fintype Z]
    {N n : ℕ} (c : WiretapFeedback.WiretapCode X Y N n) (μ : PMF (Fin N))
    (W V : WildeQIT.Channel X (Y × Z)) (ε' : ℝ) (h0 : 0 ≤ ε') (h1 : ε' < 1) :
    WiretapFeedback.negLog2 (WiretapFeedback.testBeta ε' (c.law μ W) (c.law μ V)) ≤
      WiretapFeedback.negLog2 (WiretapFeedback.activeBeta ε' W V n) := by
  have hle : WiretapFeedback.activeBeta ε' W V n ≤
      WiretapFeedback.testBeta ε' (c.law μ W) (c.law μ V) := by
    refine (iInf_le _ (c.toStrategy Z μ)).trans ?_
    unfold WiretapFeedback.testBeta
    refine le_iInf fun T => le_iInf fun hT => le_iInf fun hP => ?_
    refine iInf_le_of_le (simTest c μ T) (iInf_le_of_le (fun b => simTest_le_one c μ T hT b)
      (iInf_le_of_le ?_ (le_of_eq (obs_eq_law c μ V T hT))))
    rw [obs_eq_law c μ W T hT]
    exact hP
  have hlog2 : (0 : EReal) ≤ (((Real.log 2)⁻¹ : ℝ) : EReal) := by
    exact_mod_cast (inv_nonneg.mpr (Real.log_nonneg (by norm_num)))
  unfold WiretapFeedback.negLog2
  exact mul_le_mul_of_nonneg_right (EReal.neg_le_neg_iff.mpr (ENNReal.log_le_log hle)) hlog2
