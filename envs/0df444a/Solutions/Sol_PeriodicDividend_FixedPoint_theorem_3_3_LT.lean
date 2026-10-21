-- Prove2me | solution 1 for PeriodicDividend.FixedPoint.theorem_3_3_LT
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:59:06.942211+00:00
-- url     : https://prove2.me/submissions/a2ceff45-7279-4263-95b8-bdfa70188ae4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model
import Theorems.Thm_PeriodicDividend_FixedPoint_theorem_3_3_D
import Theorems.Thm_PeriodicDividend_FixedPoint_theorem_3_6
import Theorems.Thm_PeriodicDividend_FixedPoint_L_eq_vOneExtended_T

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace PDSol33LT
open PeriodicDividend.FixedPoint

/-! ### Elementary facts on `D` and `I` -/

lemma D_bdd (φ : ℝ≥0 → ℝ) (A : ℝ) (hb : ∀ y, φ y ≤ (y : ℝ) + A) (x : ℝ≥0) :
    BddAbove {y : ℝ | ∃ d : ℝ≥0, d ≤ x ∧ y = φ (x - d) + (d : ℝ)} := by
  refine ⟨(x : ℝ) + A, ?_⟩
  rintro y ⟨d, hd, rfl⟩
  have h1 := hb (x - d)
  rw [NNReal.coe_sub hd] at h1
  linarith

lemma le_D (φ : ℝ≥0 → ℝ) (A : ℝ) (hb : ∀ y, φ y ≤ (y : ℝ) + A) (x y : ℝ≥0)
    (hy : y ≤ x) : φ y + ((x : ℝ) - y) ≤ Dop φ x := by
  apply le_csSup (D_bdd φ A hb x)
  refine ⟨x - y, tsub_le_self, ?_⟩
  rw [tsub_tsub_cancel_of_le hy, NNReal.coe_sub hy]

lemma D_le (φ : ℝ≥0 → ℝ) (x : ℝ≥0) (c : ℝ)
    (h : ∀ y : ℝ≥0, y ≤ x → φ y + ((x : ℝ) - y) ≤ c) : Dop φ x ≤ c := by
  refine csSup_le ⟨_, 0, zero_le, rfl⟩ ?_
  rintro w ⟨d, hd, rfl⟩
  have := h (x - d) tsub_le_self
  rw [NNReal.coe_sub hd] at this
  linarith

lemma Dop_shift (a b : ℝ≥0 → ℝ) (A K : ℝ) (hb : ∀ y, b y ≤ (y : ℝ) + A)
    (ha : ∀ y, a y ≤ b y + K) (x : ℝ≥0) : Dop a x ≤ Dop b x + K :=
  D_le a x _ (fun y hy => by have := le_D b A hb x y hy; have := ha y; linarith)

lemma Iop_nonempty (p : Params) (ψ : ℝ≥0 → ℝ) (x : ℝ≥0) :
    ({y : ℝ | ∃ z : ℝ≥0, 0 < z ∧ y = ψ (x + z) - issueCost p z}).Nonempty :=
  ⟨_, 1, one_pos, rfl⟩

/-! ### Extended-real bookkeeping -/

lemma ereal_issue_aux (u a b : ℝ≥0∞) (ha : a ≠ ⊤) :
    (u : EReal) - b ≤ ((u : EReal) - ((a + b : ℝ≥0∞) : EReal)) + (a.toReal : EReal) := by
  induction b using ENNReal.recTopCoe with
  | top => simp [EReal.sub_top]
  | coe r =>
    lift a to ℝ≥0 using ha
    induction u using ENNReal.recTopCoe with
    | top =>
      rw [EReal.coe_ennreal_top, ← ENNReal.coe_add, EReal.coe_nnreal_eq_coe_real,
        EReal.coe_nnreal_eq_coe_real, EReal.top_sub_coe, EReal.top_sub_coe, EReal.top_add_coe]
    | coe w =>
      rw [← ENNReal.coe_add]
      simp only [EReal.coe_nnreal_eq_coe_real, ENNReal.coe_toReal, NNReal.coe_add]
      rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith

lemma ereal_shift_aux (u v c : ℝ≥0∞) (k : ℝ) (hk : 0 ≤ k) (h : u ≤ v + ENNReal.ofReal k) :
    (u : EReal) - c ≤ ((v : EReal) - c) + (k : EReal) := by
  have h1 : (u : EReal) ≤ (v : EReal) + (k : EReal) := by
    have := (EReal.coe_ennreal_le_coe_ennreal_iff).mpr h
    rwa [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal, max_eq_left hk] at this
  calc (u : EReal) - c ≤ ((v : EReal) + (k : EReal)) - c := EReal.sub_le_sub h1 le_rfl
    _ = ((v : EReal) - c) + (k : EReal) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, add_right_comm]

/-! ### Comparison of one-period payoffs: `L(φ) ≤ L(ψ) + e^{-ρT} K` -/

lemma terminalReward_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : ℝ → Ω → ℝ) (p : Params) (φ ψ : ℝ≥0 → ℝ) (K : ℝ)
    (h : ∀ y, φ y ≤ ψ y + K) (x : ℝ≥0) (I : Issuance Ω) :
    terminalReward P C p φ x I p.T true ≤
      terminalReward P C p ψ x I p.T true + ENNReal.ofReal (Real.exp (-p.rho * p.T) * K) := by
  unfold terminalReward
  have he := Real.exp_pos (-p.rho * p.T)
  calc _ ≤ ∫⁻ ω, ((if (if true = true then ENNReal.ofReal p.T < ruin C p x (noDividends Ω) I ω
        else ENNReal.ofReal p.T ≤ ruin C p x (noDividends Ω) I ω) then
          ENNReal.ofReal (Real.exp (-p.rho * p.T) *
            ψ (Real.toNNReal (oneReserveBefore C x I p.T ω))) else 0) +
          ENNReal.ofReal (Real.exp (-p.rho * p.T) * K)) ∂P := by
        apply lintegral_mono
        intro ω
        dsimp only
        split_ifs
        all_goals first
          | exact zero_le
          | (refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
             have := mul_le_mul_of_nonneg_left (h (Real.toNNReal (oneReserveBefore C x I p.T ω))) he.le
             linarith)
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

lemma onePayoff_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : ℝ → Ω → ℝ) (p : Params) (φ ψ : ℝ≥0 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ y, φ y ≤ ψ y + K) (x : ℝ≥0) (I : Issuance Ω) :
    onePayoff P C p φ x I ≤
      onePayoff P C p ψ x I + ((Real.exp (-p.rho * p.T) * K : ℝ) : EReal) := by
  unfold onePayoff
  exact ereal_shift_aux _ _ _ _ (mul_nonneg (Real.exp_pos _).le hK)
    (terminalReward_le P C p φ ψ K h x I)

lemma Lop_le {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params) (φ ψ : ℝ≥0 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ y, φ y ≤ ψ y + K) (x : ℝ≥0) :
    Lop P 𝔽 C p φ x ≤ Lop P 𝔽 C p ψ x + ((Real.exp (-p.rho * p.T) * K : ℝ) : EReal) := by
  apply sSup_le
  rintro y ⟨I, hI, rfl⟩
  have hmem : onePayoff P C p ψ x I ≤ Lop P 𝔽 C p ψ x := by
    unfold Lop; exact le_sSup ⟨I, hI, rfl⟩
  exact le_trans (onePayoff_le P C p φ ψ K hK h x I) (add_le_add hmem le_rfl)

/-! ### Immediate issuance: `L φ(x + z) ≤ L φ(x) + c(z)` -/

/-- Prepend an issue of size `z` at time `0` to an issuance policy. -/
def shτ {Ω : Type*} (I : Issuance Ω) : ℕ → Ω → ℝ≥0∞
  | 0 => fun _ => 0
  | k + 1 => I.τ k

def shζ {Ω : Type*} (I : Issuance Ω) (z : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => z
  | k + 1 => I.ζ k

def shI {Ω : Type*} (I : Issuance Ω) (z : ℝ) : Issuance Ω := ⟨shτ I, shζ I z⟩

lemma issuedThrough_sh {Ω : Type*} (I : Issuance Ω) (z t : ℝ) (ω : Ω)
    (hfin : {k | I.τ k ω ≤ ENNReal.ofReal t}.Finite) :
    issuedThrough (shI I z) t ω = z + issuedThrough I t ω := by
  unfold issuedThrough
  have hs : Summable (fun k => if (shI I z).τ k ω ≤ ENNReal.ofReal t then (shI I z).ζ k ω else 0) := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset ((hfin.image Nat.succ).insert 0)
    intro k hk
    rcases k with _ | k
    · exact Set.mem_insert _ _
    · right
      refine ⟨k, ?_, rfl⟩
      by_contra hc
      apply hk
      show (if I.τ k ω ≤ ENNReal.ofReal t then I.ζ k ω else 0) = 0
      exact if_neg hc
  rw [hs.tsum_eq_zero_add]
  simp [shI, shτ, shζ]
  try rfl

lemma issuedBefore_sh {Ω : Type*} (I : Issuance Ω) (z t : ℝ) (ht : 0 < t) (ω : Ω)
    (hfin : {k | I.τ k ω ≤ ENNReal.ofReal t}.Finite) :
    issuedBefore (shI I z) t ω = z + issuedBefore I t ω := by
  unfold issuedBefore
  have hs : Summable (fun k => if (shI I z).τ k ω < ENNReal.ofReal t then (shI I z).ζ k ω else 0) := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset ((hfin.image Nat.succ).insert 0)
    intro k hk
    rcases k with _ | k
    · exact Set.mem_insert _ _
    · right
      refine ⟨k, ?_, rfl⟩
      by_contra hc
      apply hk
      show (if I.τ k ω < ENNReal.ofReal t then I.ζ k ω else 0) = 0
      exact if_neg (fun h' => hc (le_of_lt h'))
  rw [hs.tsum_eq_zero_add]
  have : (0 : ℝ≥0∞) < ENNReal.ofReal t := ENNReal.ofReal_pos.mpr ht
  simp [shI, shτ, shζ, this]
  try rfl

lemma paidBefore_zero {Ω : Type*} (p : Params) (t : ℝ) (ω : Ω) :
    paidBefore p (noDividends Ω) t ω = 0 := by
  simp [paidBefore, noDividends]

lemma paidThrough_zero {Ω : Type*} (p : Params) (t : ℝ) (ω : Ω) :
    paidThrough p (noDividends Ω) t ω = 0 := by
  simp [paidThrough, noDividends]

lemma ruin_sh {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝔽 : Filtration ℝ mΩ)
    (C : ℝ → Ω → ℝ) (p : Params) (x z : ℝ≥0) (I : Issuance Ω)
    (hI : Admissible 𝔽 C p (x + z) (noDividends Ω) I) :
    ruin C p x (noDividends Ω) (shI I z) = ruin C p (x + z) (noDividends Ω) I := by
  funext ω
  unfold ruin
  congr 2
  ext t
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨ht, hr⟩
    refine ⟨ht, ?_⟩
    unfold reserve at hr ⊢
    rw [issuedThrough_sh I z t ω (hI.2.2.2.2.1 ω t ht.le)] at hr
    push_cast; linarith
  · rintro ⟨ht, hr⟩
    refine ⟨ht, ?_⟩
    unfold reserve at hr ⊢
    rw [issuedThrough_sh I z t ω (hI.2.2.2.2.1 ω t ht.le)]
    push_cast at hr; linarith

lemma admissible_sh {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝔽 : Filtration ℝ mΩ)
    (C : ℝ → Ω → ℝ) (p : Params) (hT : 0 < p.T) (hC0 : ∀ ω, C 0 ω = 0)
    (x z : ℝ≥0) (I : Issuance Ω)
    (hI : Admissible 𝔽 C p (x + z) (noDividends Ω) I) :
    Admissible 𝔽 C p x (noDividends Ω) (shI I z) := by
  have hruin := ruin_sh 𝔽 C p x z I hI
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h7, ?_⟩
  · intro k t ht
    rcases k with _ | k
    · simp only [shI, shτ, zero_le, Set.setOf_true]; exact MeasurableSet.univ
    · exact h1 k t ht
  · intro k t ht
    rcases k with _ | k
    · simp only [shI, shτ, shζ, zero_le, if_true]; exact stronglyMeasurable_const
    · exact h2 k t ht
  · intro k ω
    rcases k with _ | k
    · exact z.2
    · exact h3 k ω
  · intro k ω
    rcases k with _ | k
    · exact zero_le
    · exact h4 k ω
  · intro ω t ht
    apply Set.Finite.subset (((h5 ω t ht).image Nat.succ).insert 0)
    intro k hk
    rcases k with _ | k
    · exact Set.mem_insert _ _
    · exact Or.inr ⟨k, hk, rfl⟩
  · intro k ω hk
    rw [hruin]
    rcases k with _ | k
    · exact zero_le
    · exact h6 k ω hk
  · intro n ω
    refine ⟨le_rfl, fun hn => ?_, fun _ => rfl⟩
    show (0 : ℝ) ≤ _
    rcases n with _ | n
    · unfold reserveBefore
      rw [paidBefore_zero]
      have hnn : 0 ≤ issuedBefore (shI I z) ((((0 : ℕ) : ℝ)) * p.T) ω := by
        unfold issuedBefore
        apply tsum_nonneg
        intro k
        split_ifs
        · rcases k with _ | k
          · exact z.2
          · exact h3 k ω
        · exact le_rfl
      simp only [Nat.cast_zero, zero_mul, hC0] at hnn ⊢
      have := x.2
      linarith
    · have htpos : 0 < ((n + 1 : ℕ) : ℝ) * p.T := by positivity
      rw [hruin] at hn
      have := (h8 (n + 1) ω).2.1 hn
      have hfin := h5 ω _ htpos.le
      unfold reserveBefore at this ⊢
      rw [issuedBefore_sh I z _ htpos ω hfin]
      simp only [noDividends] at this
      push_cast at this ⊢
      linarith

lemma costBefore_sh {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : Params) (hT : 0 < p.T) (I : Issuance Ω) (z : ℝ) :
    costBefore P p (shI I z) p.T = ENNReal.ofReal (issueCost p z) + costBefore P p I p.T := by
  unfold costBefore
  have : ∀ ω, (∑' k, if (shI I z).τ k ω < ENNReal.ofReal p.T then ENNReal.ofReal
      (Real.exp (-p.rho * ((shI I z).τ k ω).toReal) * issueCost p ((shI I z).ζ k ω)) else 0) =
      ENNReal.ofReal (issueCost p z) + ∑' k, if I.τ k ω < ENNReal.ofReal p.T then ENNReal.ofReal
      (Real.exp (-p.rho * (I.τ k ω).toReal) * issueCost p (I.ζ k ω)) else 0 := by
    intro ω
    rw [tsum_eq_zero_add' ENNReal.summable]
    have h0 : (0 : ℝ≥0∞) < ENNReal.ofReal p.T := ENNReal.ofReal_pos.mpr hT
    simp [shI, shτ, shζ, h0]
  simp_rw [this]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

lemma terminalReward_sh {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params) (hT : 0 < p.T) (φ : ℝ≥0 → ℝ)
    (x z : ℝ≥0) (I : Issuance Ω) (hI : Admissible 𝔽 C p (x + z) (noDividends Ω) I) :
    terminalReward P C p φ x (shI I z) p.T true =
      terminalReward P C p φ (x + z) I p.T true := by
  have hruin := ruin_sh 𝔽 C p x z I hI
  have hres : ∀ ω, oneReserveBefore C x (shI I z) p.T ω = oneReserveBefore C (x + z) I p.T ω := by
    intro ω
    unfold oneReserveBefore
    rw [issuedBefore_sh I z p.T hT ω (hI.2.2.2.2.1 ω p.T hT.le)]
    push_cast; ring
  unfold terminalReward
  simp only [hruin, hres]

lemma issueCost_pos (p : Params) (hS : p.Standing) (z : ℝ) (hz : 0 < z) : 0 < issueCost p z := by
  obtain ⟨_, _, _, hF, hP, _⟩ := hS
  simp only [issueCost, hz, if_true]
  nlinarith

lemma Lop_issue {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params) (hS : p.Standing)
    (hC0 : ∀ ω, C 0 ω = 0) (φ : ℝ≥0 → ℝ) (x z : ℝ≥0) (hz : 0 < z) :
    Lop P 𝔽 C p φ (x + z) ≤ Lop P 𝔽 C p φ x + ((issueCost p z : ℝ) : EReal) := by
  have hT : 0 < p.T := hS.2.2.2.2.2
  apply sSup_le
  rintro y ⟨I, hI, rfl⟩
  have hadm := admissible_sh 𝔽 C p hT hC0 x z I hI
  have hc := issueCost_pos p hS z hz
  calc onePayoff P C p φ (x + z) I
      ≤ onePayoff P C p φ x (shI I z) + ((issueCost p z : ℝ) : EReal) := by
        unfold onePayoff
        rw [terminalReward_sh P 𝔽 C p hT φ x z I hI, costBefore_sh P p hT I z]
        have := ereal_issue_aux (terminalReward P C p φ (x + z) I p.T true)
          (ENNReal.ofReal (issueCost p z)) (costBefore P p I p.T) ENNReal.ofReal_ne_top
        rwa [ENNReal.toReal_ofReal hc.le] at this
    _ ≤ Lop P 𝔽 C p φ x + ((issueCost p z : ℝ) : EReal) := by
        have hmem : onePayoff P C p φ x (shI I z) ≤ Lop P 𝔽 C p φ x := by
          unfold Lop; exact le_sSup ⟨shI I z, hadm, rfl⟩
        exact add_le_add hmem le_rfl

end PDSol33LT

open PDSol33LT PeriodicDividend.FixedPoint in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : PeriodicDividend.FixedPoint.Params)
    (hS : p.Standing)
    (hU : PeriodicDividend.FixedPoint.UsualConditions P 𝔽)
    (hC : AtaBarjesteh23.Workload.IsDriftBM 𝔽 P C p.mu p.sigma)
    (A : ℝ) (hA : PeriodicDividend.FixedPoint.Astar p ≤ A) :
    (∀ φ : ℝ≥0 → ℝ, PeriodicDividend.FixedPoint.CA p A φ →
      PeriodicDividend.FixedPoint.ChatA p A
        (fun x => (PeriodicDividend.FixedPoint.Lop P 𝔽 C p φ x).toReal) ∧
      PeriodicDividend.FixedPoint.CA p A (PeriodicDividend.FixedPoint.Top P 𝔽 C p φ)) ∧
    (∀ (φ ψ : ℝ≥0 → ℝ) (K : ℝ),
      PeriodicDividend.FixedPoint.CA p A φ → PeriodicDividend.FixedPoint.CA p A ψ →
      (∀ x, |φ x - ψ x| ≤ K) →
      ∀ x, |PeriodicDividend.FixedPoint.Top P 𝔽 C p φ x -
        PeriodicDividend.FixedPoint.Top P 𝔽 C p ψ x| ≤
        Real.exp (-p.rho * p.T) * K) := by
  obtain ⟨hρ, hμ, hσ, hF, hP, hT⟩ := hS
  have hS' : p.Standing := ⟨hρ, hμ, hσ, hF, hP, hT⟩
  have hC0 : ∀ ω, C 0 ω = 0 := hC.1
  have hTmem : p.T ∈ Icc (0 : ℝ) p.T := ⟨hT.le, le_rfl⟩
  set e := Real.exp (-p.rho * p.T) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := by
    rw [he, Real.exp_le_one_iff]; nlinarith [mul_pos hρ hT]
  -- `e (A + μ T) ≤ A`, from `A ≥ A*`
  have hE : 1 < Real.exp (p.rho * p.T) := Real.one_lt_exp_iff.mpr (mul_pos hρ hT)
  have hAs : p.mu * p.T ≤ (Real.exp (p.rho * p.T) - 1) * A := by
    have := hA
    unfold Astar at this
    rw [div_le_iff₀ (by linarith)] at this
    linarith
  have hprod : e * Real.exp (p.rho * p.T) = 1 := by
    rw [he, ← Real.exp_add]; simp
  have hEA : e * (A + p.mu * p.T) ≤ A := by
    calc e * (A + p.mu * p.T) ≤ e * (A + (Real.exp (p.rho * p.T) - 1) * A) :=
          mul_le_mul_of_nonneg_left (by linarith) he0.le
      _ = (e * Real.exp (p.rho * p.T)) * A := by ring
      _ = A := by rw [hprod, one_mul]
  have hA0 : 0 ≤ A := by
    have : 0 ≤ Astar p := by
      unfold Astar
      exact div_nonneg (mul_pos hμ hT).le (by linarith)
    linarith
  -- the key properties of `L φ` for `φ ∈ C_A`
  have key : ∀ φ : ℝ≥0 → ℝ, CA p A φ →
      (∀ x, Lop P 𝔽 C p φ x = (((Lop P 𝔽 C p φ x).toReal : ℝ) : EReal)) ∧
      ChatA p A (fun x => (Lop P 𝔽 C p φ x).toReal) := by
    intro φ hφ
    have hlink := fun x => L_eq_vOneExtended_T P 𝔽 C p hS' hU hC A φ hφ x
    have h36 := theorem_3_6 P 𝔽 C p hS' hU hC A hA φ hφ
    obtain ⟨hfin, -, hcont, hCTA, -, hbd, -, -⟩ := h36
    have hfun : (fun x => (Lop P 𝔽 C p φ x).toReal) = vOne P 𝔽 C p φ p.T := by
      funext x; rw [hlink x]; rfl
    refine ⟨fun x => ?_, ?_⟩
    · rw [hlink x]
      exact (EReal.coe_toReal (hfin p.T hTmem x).1 (hfin p.T hTmem x).2).symm
    rw [hfun]
    -- continuity
    have hc : Continuous (vOne P 𝔽 C p φ p.T) := by
      have hg : Continuous (fun x : ℝ≥0 => ((p.T, (x : ℝ)) : ℝ × ℝ)) := by fun_prop
      have := hcont.comp_continuous hg (fun x => ⟨hTmem, x.2⟩)
      simpa [Function.comp_def, Real.toNNReal_coe] using this
    have hmono : Monotone (vOne P 𝔽 C p φ p.T) := by
      intro a b hab
      have h1 := hCTA.1 p.T hTmem hab
      have h2 : e * (a : ℝ) ≤ e * b := mul_le_mul_of_nonneg_left (by exact_mod_cast hab) he0.le
      simp only at h1
      linarith
    have hbnd : ∀ x : ℝ≥0, 0 ≤ vOne P 𝔽 C p φ p.T x ∧ vOne P 𝔽 C p φ p.T x ≤ (x : ℝ) + A := by
      intro x
      obtain ⟨hl, hu⟩ := hCTA.2 p.T hTmem x
      have hx := x.2
      constructor
      · nlinarith
      · have : e * (x : ℝ) ≤ x := by nlinarith
        nlinarith
    have hIop : ∀ x : ℝ≥0, Iop p (vOne P 𝔽 C p φ p.T) x ≤ vOne P 𝔽 C p φ p.T x := by
      intro x
      apply csSup_le (Iop_nonempty p _ x)
      rintro w ⟨z, hz, rfl⟩
      have h1 := Lop_issue P 𝔽 C p hS' hC0 φ x z hz
      have hfx := hfin p.T hTmem x
      have hfxz := hfin p.T hTmem (x + z)
      rw [hlink, hlink] at h1
      rw [← EReal.coe_toReal hfxz.1 hfxz.2, ← EReal.coe_toReal hfx.1 hfx.2, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at h1
      show (vOneExtended P 𝔽 C p φ p.T (x + z)).toReal - issueCost p z ≤
        (vOneExtended P 𝔽 C p φ p.T x).toReal
      linarith
    exact ⟨hc, hmono, fun x => ⟨(hbnd x).1, max_le (hIop x) (hbnd x).1, (hbnd x).2⟩,
      hbd p.T hTmem⟩
  refine ⟨fun φ hφ => ⟨(key φ hφ).2, theorem_3_3_D p hS' A hA0 _ (key φ hφ).2⟩, ?_⟩
  intro φ ψ K hφ hψ hK x
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  obtain ⟨hfφ, hcφ⟩ := key φ hφ
  obtain ⟨hfψ, hcψ⟩ := key ψ hψ
  have hbφ : ∀ y : ℝ≥0, (Lop P 𝔽 C p φ y).toReal ≤ (y : ℝ) + A := fun y => (hcφ.2.2.1 y).2.2
  have hbψ : ∀ y : ℝ≥0, (Lop P 𝔽 C p ψ y).toReal ≤ (y : ℝ) + A := fun y => (hcψ.2.2.1 y).2.2
  have hcmp : ∀ (f g : ℝ≥0 → ℝ),
      (∀ y, Lop P 𝔽 C p f y = (((Lop P 𝔽 C p f y).toReal : ℝ) : EReal)) →
      (∀ y, Lop P 𝔽 C p g y = (((Lop P 𝔽 C p g y).toReal : ℝ) : EReal)) →
      (∀ y, f y ≤ g y + K) →
      ∀ y, (Lop P 𝔽 C p f y).toReal ≤ (Lop P 𝔽 C p g y).toReal + e * K := by
    intro f g hf hg hfg y
    have := Lop_le P 𝔽 C p f g K hK0 hfg y
    rw [hf y, hg y, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  have h1 := hcmp φ ψ hfφ hfψ (fun y => by have := hK y; rw [abs_le] at this; linarith)
  have h2 := hcmp ψ φ hfψ hfφ (fun y => by have := hK y; rw [abs_le] at this; linarith)
  have d1 := Dop_shift _ _ A (e * K) hbψ h1 x
  have d2 := Dop_shift _ _ A (e * K) hbφ h2 x
  show |Dop _ x - Dop _ x| ≤ e * K
  rw [abs_le]
  constructor <;> linarith
