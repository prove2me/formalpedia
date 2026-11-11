-- Prove2me | solution 1 for OceanPlastic.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T14:35:06.319314+00:00
-- url     : https://prove2.me/submissions/174bfee0-578e-479c-a77c-d9428ddcac5d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Continuity
import Definitions.Def_OceanPlastic_Problem4
import Definitions.Def_OceanPlastic_Params
import Definitions.Def_OceanPlastic_Benchmark
import Definitions.Def_OceanPlastic_CaseO

namespace S14Ocean

/-- The original model after writing `a = M/(2k)` and `b = vbar/Q`. -/
structure Model where
  a : ℝ
  b : ℝ
  v : ℝ
  q : ℝ
  δ : ℝ
  p : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  v_pos : 0 < v
  q_pos : 0 < q
  bq : b * q = v
  δ_nonneg : 0 ≤ δ
  δ_lt_one : δ < 1
  p_nonneg : 0 ≤ p

namespace Model

def profit (M : Model) (r d : ℝ) : ℝ :=
  (M.v + M.δ * r - M.b * d) * d - M.a * r * (M.p + r)

def feasible (M : Model) (z r d : ℝ) : Prop :=
  d ≤ M.a * (r + z) ∧ 0 ≤ d ∧ d ≤ M.q ∧ 0 ≤ r

def optimal (M : Model) (z r d : ℝ) : Prop :=
  M.feasible z r d ∧ ∀ r' d', M.feasible z r' d' → M.profit r' d' ≤ M.profit r d

def A (M : Model) : ℝ := 1 - M.δ + M.a * M.b
def C (M : Model) : ℝ := 1 - M.δ + 2 * M.a * M.b
noncomputable def bonusAdd (M : Model) : ℝ := max 0 ((M.v - M.p) / (2 * M.A))
noncomputable def bonusNo (M : Model) : ℝ := max 0 ((M.v - M.p * M.C) / (2 * M.A))

theorem A_pos (M : Model) : 0 < M.A := by
  have h := mul_pos M.a_pos M.b_pos
  dsimp [A]
  linarith [M.δ_lt_one]

theorem C_pos (M : Model) : 0 < M.C := by
  have h := mul_pos M.a_pos M.b_pos
  dsimp [C]
  linarith [M.δ_lt_one]

theorem zero_feasible (M : Model) {z : ℝ} (hz : 0 ≤ z) : M.feasible z 0 0 := by
  refine ⟨?_, le_rfl, le_of_lt M.q_pos, le_rfl⟩
  simpa using mul_nonneg (le_of_lt M.a_pos) hz

/-- Reducing a bonus while maintaining the capacity constraint improves profit.
The equality case is strict unless the bonus was already minimal. -/
theorem profit_reduce (M : Model) {r s d : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r)
    (hd : 0 ≤ d) (hcap : d ≤ M.a * (s + M.p)) :
    M.profit r d ≤ M.profit s d ∧
      (M.profit s d ≤ M.profit r d → r = s) := by
  have hr : 0 ≤ r := le_trans hs hsr
  have hδ : 0 < 1 - M.δ := sub_pos.mpr M.δ_lt_one
  have hc : M.a * r ≤ M.a * (r + s + M.p) - M.δ * d := by
    have ht := mul_nonneg (le_of_lt hδ) hd
    nlinarith
  have hcoef : 0 ≤ M.a * (r + s + M.p) - M.δ * d :=
    le_trans (mul_nonneg (le_of_lt M.a_pos) hr) hc
  have heq : M.profit s d - M.profit r d =
      (r - s) * (M.a * (r + s + M.p) - M.δ * d) := by
    unfold profit
    ring
  constructor
  · have ht := mul_nonneg (sub_nonneg.mpr hsr) hcoef
    linarith
  · intro hrev
    by_contra hne
    have hrs : s < r := lt_of_le_of_ne hsr (Ne.symm hne)
    have hrpos : 0 < r := lt_of_le_of_lt hs hrs
    have hcpos : 0 < M.a * (r + s + M.p) - M.δ * d :=
      lt_of_lt_of_le (mul_pos M.a_pos hrpos) hc
    have ht := mul_pos (sub_pos.mpr hrs) hcpos
    linarith

end Model
end S14Ocean

namespace S14Ocean.Model

/-- Truncate an unnecessarily large bonus. This leaves a compact rectangle
on which the continuous objective attains a maximum. -/
theorem exists_optimal (M : S14Ocean.Model) {z : ℝ} (hz : 0 ≤ z) :
    ∃ r d : ℝ, M.optimal z r d := by
  let R := M.q / M.a
  have hR : 0 ≤ R := le_of_lt (div_pos M.q_pos M.a_pos)
  have haR : M.a * R = M.q := by
    dsimp [R]
    field_simp [M.a_pos.ne']
  let K : Set (ℝ × ℝ) :=
    (Set.Icc 0 R ×ˢ Set.Icc 0 M.q) ∩ {x | x.2 ≤ M.a * (x.1 + z)}
  have hK : IsCompact K := by
    apply (isCompact_Icc.prod isCompact_Icc).inter_right
    exact isClosed_le continuous_snd (continuous_const.mul (continuous_fst.add continuous_const))
  have hn : K.Nonempty := by
    refine ⟨(0, 0), ⟨⟨⟨le_rfl, hR⟩, ⟨le_rfl, le_of_lt M.q_pos⟩⟩, ?_⟩⟩
    simpa using mul_nonneg (le_of_lt M.a_pos) hz
  have hc : Continuous (fun x : ℝ × ℝ => M.profit x.1 x.2) := by
    unfold profit
    continuity
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hn hc.continuousOn
  refine ⟨x.1, x.2, ⟨?_, ?_⟩⟩
  · exact ⟨hx.2, hx.1.2.1, hx.1.2.2, hx.1.1.1⟩
  · intro r d hrd
    by_cases hr : r ≤ R
    · exact hmax (show (r, d) ∈ K from
        ⟨⟨⟨hrd.2.2.2, hr⟩, ⟨hrd.2.1, hrd.2.2.1⟩⟩, hrd.1⟩)
    · have hRr : R ≤ r := le_of_lt (lt_of_not_ge hr)
      have hcap : d ≤ M.a * (R + M.p) := by
        have hp := mul_nonneg (le_of_lt M.a_pos) M.p_nonneg
        nlinarith [hrd.2.2.1]
      have hzcap : d ≤ M.a * (R + z) := by
        have hp := mul_nonneg (le_of_lt M.a_pos) hz
        nlinarith [hrd.2.2.1]
      have hred := (M.profit_reduce hR hRr hrd.2.1 hcap).1
      have hRmax : M.profit R d ≤ M.profit x.1 x.2 :=
        hmax (show (R, d) ∈ K from
          ⟨⟨⟨hR, le_rfl⟩, ⟨hrd.2.1, hrd.2.2.1⟩⟩, hzcap⟩)
      exact le_trans hred hRmax

end S14Ocean.Model

namespace S14Ocean.Model

theorem gap_identity (M : S14Ocean.Model) {z r₀ d₀ r d : ℝ}
    (hd₀ : d₀ = M.a * (r₀ + z)) :
    M.a * (M.profit r₀ d₀ - M.profit r d) =
      M.A * (d - d₀) ^ 2 +
      (M.a * (r + z) - d) *
        (M.a * r + M.a * (M.p - z) + (1 - M.δ) * d) +
      (d₀ - d) * (M.a * (M.v - M.p + (2 - M.δ) * z) - 2 * M.A * d₀) := by
  rw [hd₀]
  unfold profit A
  ring

/-- The capacity-boundary stationary point is the unique optimizer in bonus. -/
theorem boundary_optimal_unique (M : S14Ocean.Model) {z r₀ d₀ : ℝ}
    (hz : 0 ≤ z) (hzp : z ≤ M.p) (hr₀ : 0 ≤ r₀) (hdq : d₀ ≤ M.q)
    (hd₀ : d₀ = M.a * (r₀ + z))
    (hstation : M.a * (M.v - M.p + (2 - M.δ) * z) = 2 * M.A * d₀) :
    M.optimal z r₀ d₀ ∧ ∀ r d, M.optimal z r d → r = r₀ := by
  have hdnonneg : 0 ≤ d₀ := by
    rw [hd₀]
    exact mul_nonneg (le_of_lt M.a_pos) (add_nonneg hr₀ hz)
  have hfeas : M.feasible z r₀ d₀ := ⟨le_of_eq hd₀, hdnonneg, hdq, hr₀⟩
  have hgap : ∀ r d, M.feasible z r d →
      M.A * (d - d₀) ^ 2 ≤ M.a * (M.profit r₀ d₀ - M.profit r d) := by
    intro r d hf
    have hc : 0 ≤ M.a * r + M.a * (M.p - z) + (1 - M.δ) * d :=
      add_nonneg (add_nonneg (mul_nonneg (le_of_lt M.a_pos) hf.2.2.2)
        (mul_nonneg (le_of_lt M.a_pos) (sub_nonneg.mpr hzp)))
        (mul_nonneg (le_of_lt (sub_pos.mpr M.δ_lt_one)) hf.2.1)
    have ht := mul_nonneg (sub_nonneg.mpr hf.1) hc
    have hi := M.gap_identity (r := r) (d := d) hd₀
    rw [hstation, sub_self, mul_zero, add_zero] at hi
    linarith
  constructor
  · refine ⟨hfeas, ?_⟩
    intro r d hf
    have h := hgap r d hf
    have hs := mul_nonneg (le_of_lt M.A_pos) (sq_nonneg (d - d₀))
    nlinarith [M.a_pos]
  · intro r d ho
    have h := hgap r d ho.1
    have hrev := ho.2 r₀ d₀ hfeas
    have hAsq : M.A * (d - d₀) ^ 2 ≤ M.A * 0 := by
      have ht := mul_nonpos_of_nonneg_of_nonpos (le_of_lt M.a_pos) (sub_nonpos.mpr hrev)
      nlinarith
    have hs : (d - d₀) ^ 2 ≤ 0 := le_of_mul_le_mul_left hAsq M.A_pos
    have hd : d = d₀ := by
      have := sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
      linarith
    subst d
    have hrs : r₀ ≤ r := le_of_mul_le_mul_left (by nlinarith [ho.1.1]) M.a_pos
    have hcap : d₀ ≤ M.a * (r₀ + M.p) := by
      rw [hd₀]
      exact mul_le_mul_of_nonneg_left (by linarith : r₀ + z ≤ r₀ + M.p) (le_of_lt M.a_pos)
    exact (M.profit_reduce hr₀ hrs hdnonneg hcap).2 hrev

theorem add_bonus_zero (M : S14Ocean.Model) {r d : ℝ} (hp : M.v ≤ M.p)
    (ho : M.optimal 0 r d) : r = 0 := by
  have hr := ho.1.2.2.2
  have hd := ho.1.2.1
  have hzero : 0 ≤ M.profit r d := by
    simpa [profit] using ho.2 0 0 (M.zero_feasible (le_refl 0))
  have hcap : 0 ≤ M.a * r - d := by simpa using sub_nonneg.mpr ho.1.1
  have hcoef : 0 ≤ M.a * r + M.a * M.p + (1 - M.δ) * d :=
    add_nonneg (add_nonneg (mul_nonneg (le_of_lt M.a_pos) hr)
      (mul_nonneg (le_of_lt M.a_pos) M.p_nonneg))
      (mul_nonneg (le_of_lt (sub_pos.mpr M.δ_lt_one)) hd)
  have hprod := mul_nonneg hcap hcoef
  have hslope := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hd)
    (mul_nonpos_of_nonneg_of_nonpos (le_of_lt M.a_pos) (sub_nonpos.mpr hp))
  have hi : -M.a * M.profit r d = M.A * d ^ 2 +
      (M.a * r - d) * (M.a * r + M.a * M.p + (1 - M.δ) * d) +
      (-d) * (M.a * (M.v - M.p)) := by unfold profit A; ring
  have hAsq : M.A * d ^ 2 ≤ M.A * 0 := by
    have ht := mul_nonneg (le_of_lt M.a_pos) hzero
    nlinarith
  have hs : d ^ 2 ≤ 0 := le_of_mul_le_mul_left hAsq M.A_pos
  have hd0 : d = 0 := sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
  subst d
  have hcap0 : 0 ≤ M.a * (0 + M.p) := by
    simpa using mul_nonneg (le_of_lt M.a_pos) M.p_nonneg
  apply (M.profit_reduce (le_refl 0) hr (le_refl 0) hcap0).2
  simpa [profit] using hzero

theorem noadd_bonus_zero (M : S14Ocean.Model) {r d : ℝ} (hp : M.v ≤ M.p * M.C)
    (ho : M.optimal M.p r d) : r = 0 := by
  have hr := ho.1.2.2.2
  have hd := ho.1.2.1
  by_cases hcap : d ≤ M.a * M.p
  · have hfeas : M.feasible M.p 0 d := by
      exact ⟨by simpa using hcap, hd, ho.1.2.2.1, le_rfl⟩
    apply (M.profit_reduce (le_refl 0) hr hd (by simpa using hcap)).2
    exact ho.2 0 d hfeas
  · have hlt : M.a * M.p < d := lt_of_not_ge hcap
    have hd₀ : 0 ≤ M.a * M.p := mul_nonneg (le_of_lt M.a_pos) M.p_nonneg
    have hfeas : M.feasible M.p 0 (M.a * M.p) :=
      ⟨by simp, hd₀, le_trans (le_of_lt hlt) ho.1.2.2.1, le_rfl⟩
    have hrev := ho.2 0 (M.a * M.p) hfeas
    have hcoef : 0 ≤ M.a * r + M.a * (M.p - M.p) + (1 - M.δ) * d := by
      have ht := mul_nonneg (le_of_lt (sub_pos.mpr M.δ_lt_one)) hd
      have hu := mul_nonneg (le_of_lt M.a_pos) hr
      simpa using add_nonneg hu ht
    have hprod := mul_nonneg (sub_nonneg.mpr ho.1.1) hcoef
    have hsl : M.a * (M.v - M.p + (2 - M.δ) * M.p) -
        2 * M.A * (M.a * M.p) ≤ 0 := by
      have ht := mul_nonpos_of_nonneg_of_nonpos (le_of_lt M.a_pos) (sub_nonpos.mpr hp)
      unfold A C at *
      nlinarith
    have hslope := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (le_of_lt hlt)) hsl
    have hi := M.gap_identity (z := M.p) (r₀ := 0) (d₀ := M.a * M.p)
      (r := r) (d := d) (by simp)
    have hsq : 0 < (d - M.a * M.p) ^ 2 := sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr hlt))
    have hAsq := mul_pos M.A_pos hsq
    have hrev' := mul_nonpos_of_nonneg_of_nonpos (le_of_lt M.a_pos) (sub_nonpos.mpr hrev)
    nlinarith

theorem bonus_add_eq (M : S14Ocean.Model) {r d : ℝ} (ho : M.optimal 0 r d) :
    r = M.bonusAdd := by
  have hA := M.A_pos
  by_cases hp : M.p < M.v
  · let r₀ := (M.v - M.p) / (2 * M.A)
    let d₀ := M.a * r₀
    have hr₀ : 0 < r₀ := div_pos (sub_pos.mpr hp) (by positivity)
    have hstation : M.a * (M.v - M.p + (2 - M.δ) * 0) = 2 * M.A * d₀ := by
      dsimp [d₀, r₀]
      field_simp [ne_of_gt hA]
      ring
    have hab : M.a * M.b < M.A := by
      dsimp [A]
      linarith [M.δ_lt_one]
    have hmass : (M.a * M.b) * M.q = M.a * M.v := by rw [mul_assoc, M.bq]
    have hbound : M.a * (M.v - M.p) ≤ (2 * M.A) * M.q := by
      have h₁ := mul_le_mul_of_nonneg_left
        (show M.v - M.p ≤ M.v by linarith [M.p_nonneg]) (le_of_lt M.a_pos)
      have h₂ := mul_le_mul_of_nonneg_right
        (show M.a * M.b ≤ 2 * M.A by linarith) (le_of_lt M.q_pos)
      rw [hmass] at h₂
      exact le_trans h₁ h₂
    have hstation' : 2 * M.A * d₀ = M.a * (M.v - M.p) := by simpa using hstation.symm
    have hdq : d₀ ≤ M.q := le_of_mul_le_mul_left
      (by rw [hstation']; exact hbound) (by positivity : 0 < 2 * M.A)
    have ht := (M.boundary_optimal_unique (z := 0) (r₀ := r₀) (d₀ := d₀)
      (le_refl 0) M.p_nonneg (le_of_lt hr₀) hdq (by simp [d₀]) hstation).2 r d ho
    simpa [bonusAdd, r₀, max_eq_right (le_of_lt hr₀)] using ht
  · have hdiv : (M.v - M.p) / (2 * M.A) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hp)) (by positivity)
    rw [bonusAdd, max_eq_left hdiv]
    exact M.add_bonus_zero (le_of_not_gt hp) ho

theorem bonus_noadd_eq (M : S14Ocean.Model) {r d : ℝ} (ho : M.optimal M.p r d) :
    r = M.bonusNo := by
  have hA := M.A_pos
  by_cases hp : M.p * M.C < M.v
  · let r₀ := (M.v - M.p * M.C) / (2 * M.A)
    let d₀ := M.a * (r₀ + M.p)
    have hr₀ : 0 < r₀ := div_pos (sub_pos.mpr hp) (by positivity)
    have hstation : M.a * (M.v - M.p + (2 - M.δ) * M.p) = 2 * M.A * d₀ := by
      dsimp [d₀, r₀]
      field_simp [ne_of_gt hA]
      unfold A C
      ring
    have hab : M.a * M.b < M.A := by
      dsimp [A]
      linarith [M.δ_lt_one]
    have hmass : (M.a * M.b) * M.q = M.a * M.v := by rw [mul_assoc, M.bq]
    have hδC : 1 - M.δ ≤ M.C := by
      have h := mul_pos M.a_pos M.b_pos
      dsimp [C]
      nlinarith
    have hδp : (1 - M.δ) * M.p < M.v := by
      have h := mul_le_mul_of_nonneg_right hδC M.p_nonneg
      nlinarith
    have hbound : M.a * (M.v - M.p + (2 - M.δ) * M.p) ≤ (2 * M.A) * M.q := by
      have h₁ := mul_le_mul_of_nonneg_left
        (show M.v - M.p + (2 - M.δ) * M.p ≤ 2 * M.v by nlinarith)
        (le_of_lt M.a_pos)
      have h₂ := mul_le_mul_of_nonneg_right
        (show 2 * (M.a * M.b) ≤ 2 * M.A by linarith) (le_of_lt M.q_pos)
      nlinarith
    have hdq : d₀ ≤ M.q := le_of_mul_le_mul_left
      (by rw [← hstation]; exact hbound) (by positivity : 0 < 2 * M.A)
    have ht := (M.boundary_optimal_unique (z := M.p) (r₀ := r₀) (d₀ := d₀)
      M.p_nonneg (le_refl M.p) (le_of_lt hr₀) hdq rfl hstation).2 r d ho
    simpa [bonusNo, r₀, max_eq_right (le_of_lt hr₀)] using ht
  · have hdiv : (M.v - M.p * M.C) / (2 * M.A) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hp)) (by positivity)
    rw [bonusNo, max_eq_left hdiv]
    exact M.noadd_bonus_zero (le_of_not_gt hp) ho

end S14Ocean.Model

namespace OceanPlastic.Params

noncomputable def normalizedModel (P : OceanPlastic.Params) : S14Ocean.Model where
  a := P.M / (2 * P.k)
  b := P.vbar / P.Q
  v := P.vbar
  q := P.Q
  δ := P.δ
  p := P.pm
  a_pos := div_pos P.M_pos (mul_pos (by norm_num) P.k_pos)
  b_pos := div_pos P.vbar_pos P.Q_pos
  v_pos := P.vbar_pos
  q_pos := P.Q_pos
  bq := div_mul_cancel₀ P.vbar P.Q_pos.ne'
  δ_nonneg := P.δ_nonneg
  δ_lt_one := P.δ_lt_one
  p_nonneg := P.pm_nonneg

theorem profit_bridge (P : OceanPlastic.Params) (r d : ℝ) :
    P.normalizedModel.profit r d = P.PiOF r d := by
  unfold normalizedModel S14Ocean.Model.profit PiOF VO
  ring

theorem feasible_bridge (P : OceanPlastic.Params) (r d : ℝ) :
    P.normalizedModel.feasible 0 r d ↔ P.Feasible r d := by
  have hv : P.VO r - P.VB = P.normalizedModel.a * r := by
    unfold VO VB normalizedModel
    ring
  change (d ≤ P.normalizedModel.a * (r + 0) ∧ 0 ≤ d ∧ d ≤ P.Q ∧ 0 ≤ r) ↔
    (d ≤ P.VO r - P.VB ∧ 0 ≤ d ∧ d ≤ P.Q ∧ 0 ≤ r)
  rw [add_zero, hv]

theorem feasibleNoAdd_bridge (P : OceanPlastic.Params) (r d : ℝ) :
    P.normalizedModel.feasible P.pm r d ↔ P.FeasibleNoAdd r d := by
  have hv : P.VO r = P.normalizedModel.a * (r + P.pm) := by
    unfold VO normalizedModel
    ring
  change (d ≤ P.normalizedModel.a * (r + P.pm) ∧ 0 ≤ d ∧ d ≤ P.Q ∧ 0 ≤ r) ↔
    (d ≤ P.VO r ∧ 0 ≤ d ∧ d ≤ P.Q ∧ 0 ≤ r)
  rw [hv]

theorem optimal_bridge (P : OceanPlastic.Params) (r d : ℝ) :
    P.IsOptimal 1 0 0 r d ↔ P.normalizedModel.optimal 0 r d := by
  simp only [IsOptimal, S14Ocean.Model.optimal, feasible_bridge, profit_bridge,
    TO, one_mul, zero_mul, add_zero]

theorem optimalNoAdd_bridge (P : OceanPlastic.Params) (r d : ℝ) :
    P.IsOptimalNoAdd 1 0 0 r d ↔ P.normalizedModel.optimal P.pm r d := by
  simp only [IsOptimalNoAdd, S14Ocean.Model.optimal, feasibleNoAdd_bridge, profit_bridge,
    TO, one_mul, zero_mul, add_zero]

theorem normalized_two_ab (P : OceanPlastic.Params) :
    2 * P.normalizedModel.a * P.normalizedModel.b = P.M * P.vbar / (P.k * P.Q) := by
  unfold normalizedModel
  field_simp

theorem market_bridge (P : OceanPlastic.Params) :
    (P.k * P.δ * P.Q ≤ P.M * P.vbar ↔
      P.δ ≤ 2 * P.normalizedModel.a * P.normalizedModel.b) := by
  rw [normalized_two_ab, le_div_iff₀ (mul_pos P.k_pos P.Q_pos)]
  constructor <;> intro h <;> nlinarith [h]

theorem market_strict_bridge (P : OceanPlastic.Params) :
    (P.M * P.vbar < P.k * P.δ * P.Q ↔
      2 * P.normalizedModel.a * P.normalizedModel.b < P.δ) := by
  rw [normalized_two_ab, div_lt_iff₀ (mul_pos P.k_pos P.Q_pos)]
  constructor <;> intro h <;> nlinarith [h]

theorem pHat_condition_bridge (P : OceanPlastic.Params) :
    (P.pm * ((1 - P.δ) * P.k * P.Q + P.M * P.vbar) < P.k * P.Q * P.vbar ↔
      P.pm * P.normalizedModel.C < P.vbar) := by
  have he : P.pm * P.normalizedModel.C =
      (P.pm * ((1 - P.δ) * P.k * P.Q + P.M * P.vbar)) / (P.k * P.Q) := by
    unfold S14Ocean.Model.C
    rw [normalized_two_ab]
    change P.pm * (1 - P.δ + P.M * P.vbar / (P.k * P.Q)) = _
    field_simp [P.k_pos.ne', P.Q_pos.ne']
  rw [he, div_lt_iff₀ (mul_pos P.k_pos P.Q_pos)]
  constructor <;> intro h <;> nlinarith [h]

theorem SO_difference (P : OceanPlastic.Params) (r s : ℝ) :
    P.SO s - P.SO r =
      ((1 + P.ρp) * P.M / (4 * P.k)) * (s - r) * (2 * P.pm + s + r) := by
  unfold SO PiOC PiOP PiBC PiBP
  ring

theorem EO_formula (P : OceanPlastic.Params) (r : ℝ) :
    P.EO r = (P.cE * P.M / (2 * P.k)) * r := by
  unfold EO VO VB
  ring

theorem SO_mono (P : OceanPlastic.Params) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    P.SO r ≤ P.SO s := by
  have hs : 0 ≤ s := le_trans hr hrs
  have hc : 0 ≤ (1 + P.ρp) * P.M / (4 * P.k) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith [P.ρp_pos]) (le_of_lt P.M_pos)
    · exact le_of_lt (mul_pos (by norm_num) P.k_pos)
  apply sub_nonneg.mp
  rw [SO_difference]
  exact mul_nonneg (mul_nonneg hc (sub_nonneg.mpr hrs))
    (by linarith [P.pm_nonneg])

theorem SO_strict (P : OceanPlastic.Params) {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) :
    P.SO r < P.SO s := by
  have hs : 0 < s := lt_of_le_of_lt hr hrs
  have hc : 0 < (1 + P.ρp) * P.M / (4 * P.k) := by
    apply div_pos
    · exact mul_pos (by linarith [P.ρp_pos]) P.M_pos
    · exact mul_pos (by norm_num) P.k_pos
  apply sub_pos.mp
  rw [SO_difference]
  exact mul_pos (mul_pos hc (sub_pos.mpr hrs))
    (by linarith [P.pm_nonneg])

theorem EO_mono (P : OceanPlastic.Params) {r s : ℝ} (hrs : r ≤ s) :
    P.EO r ≤ P.EO s := by
  rw [EO_formula, EO_formula]
  apply mul_le_mul_of_nonneg_left hrs
  exact div_nonneg (mul_nonneg P.cE_nonneg (le_of_lt P.M_pos))
    (le_of_lt (mul_pos (by norm_num) P.k_pos))

theorem EO_strict (P : OceanPlastic.Params) {r s : ℝ} (hcE : 0 < P.cE) (hrs : r < s) :
    P.EO r < P.EO s := by
  rw [EO_formula, EO_formula]
  apply mul_lt_mul_of_pos_left hrs
  exact div_pos (mul_pos hcE P.M_pos) (mul_pos (by norm_num) P.k_pos)

end OceanPlastic.Params

namespace S14Ocean.Model

theorem bonusNo_le_bonusAdd (M : S14Ocean.Model)
    (hmarket : M.δ ≤ 2 * M.a * M.b) : M.bonusNo ≤ M.bonusAdd := by
  have hC : 1 ≤ M.C := by
    dsimp [C]
    linarith
  have hprod : M.p ≤ M.p * M.C := by
    simpa using mul_le_mul_of_nonneg_left hC M.p_nonneg
  have hnum : M.v - M.p * M.C ≤ M.v - M.p := by linarith
  unfold bonusNo bonusAdd
  exact max_le_max le_rfl (div_le_div_of_nonneg_right hnum
    (le_of_lt (mul_pos (by norm_num) M.A_pos)))

theorem bonusAdd_lt_bonusNo (M : S14Ocean.Model)
    (hmarket : 2 * M.a * M.b < M.δ) (hp : 0 < M.p)
    (hprice : M.p * M.C < M.v) : M.bonusAdd < M.bonusNo := by
  have hC : M.C < 1 := by
    dsimp [C]
    linarith
  have hprod : M.p * M.C < M.p := by
    simpa using mul_lt_mul_of_pos_left hC hp
  have hnum : M.v - M.p < M.v - M.p * M.C := by linarith
  have hden : 0 < 2 * M.A := mul_pos (by norm_num) M.A_pos
  have hright : 0 < (M.v - M.p * M.C) / (2 * M.A) :=
    div_pos (sub_pos.mpr hprice) hden
  have hfrac := div_lt_div_of_pos_right hnum hden
  unfold bonusNo bonusAdd
  rw [max_eq_right (le_of_lt hright)]
  exact max_lt_iff.mpr ⟨hright, hfrac⟩

theorem bonusNo_le_bonusAdd_iff (M : S14Ocean.Model) (hp : 0 < M.p) (hpv : M.p ≤ M.v) :
    M.bonusNo ≤ M.bonusAdd ↔ M.δ ≤ 2 * M.a * M.b := by
  constructor
  · intro hle
    by_contra hn
    have hmarket : 2 * M.a * M.b < M.δ := lt_of_not_ge hn
    have hC : M.C < 1 := by
      dsimp [C]
      linarith
    have hprice : M.p * M.C < M.v := calc
      M.p * M.C < M.p := by simpa using mul_lt_mul_of_pos_left hC hp
      _ ≤ M.v := hpv
    have hlt := M.bonusAdd_lt_bonusNo hmarket hp hprice
    linarith
  · exact M.bonusNo_le_bonusAdd

end S14Ocean.Model

open OceanPlastic

theorem solution (P : Params) (hA : P.δ ^ 2 * P.k * P.Q ≤ 2 * P.M * P.vbar) :
    (∃ r d : ℝ, P.IsOptimal 1 0 0 r d) ∧
    (∃ r d : ℝ, P.IsOptimalNoAdd 1 0 0 r d) ∧
    ∀ rt dt rh dh : ℝ, P.IsOptimal 1 0 0 rt dt → P.IsOptimalNoAdd 1 0 0 rh dh →
      (P.k * P.δ * P.Q ≤ P.M * P.vbar → P.SO rt ≥ P.SO rh ∧ P.EO rt ≥ P.EO rh) ∧
      (P.M * P.vbar < P.k * P.δ * P.Q → 0 < P.pm →
        P.pm * ((1 - P.δ) * P.k * P.Q + P.M * P.vbar) < P.k * P.Q * P.vbar →
        P.SO rt < P.SO rh ∧ P.EO rt ≤ P.EO rh ∧ (0 < P.cE → P.EO rt < P.EO rh)) ∧
      (0 < P.pm → P.pm ≤ P.vbar →
        ((P.SO rt ≥ P.SO rh ∧ P.EO rt ≥ P.EO rh) ↔ P.k * P.δ * P.Q ≤ P.M * P.vbar)) := by
  let N := P.normalizedModel
  have heAdd : ∃ r d : ℝ, P.IsOptimal 1 0 0 r d := by
    obtain ⟨r, d, h⟩ := N.exists_optimal (z := 0) (le_refl 0)
    exact ⟨r, d, (P.optimal_bridge r d).mpr h⟩
  have heNo : ∃ r d : ℝ, P.IsOptimalNoAdd 1 0 0 r d := by
    obtain ⟨r, d, h⟩ := N.exists_optimal (z := P.pm) P.pm_nonneg
    exact ⟨r, d, (P.optimalNoAdd_bridge r d).mpr h⟩
  refine ⟨heAdd, heNo, ?_⟩
  intro rt dt rh dh ht hh
  have htN : N.optimal 0 rt dt := (P.optimal_bridge rt dt).mp ht
  have hhN : N.optimal N.p rh dh := (P.optimalNoAdd_bridge rh dh).mp hh
  have hrt : rt = N.bonusAdd := N.bonus_add_eq htN
  have hrh : rh = N.bonusNo := N.bonus_noadd_eq hhN
  have hrt0 : 0 ≤ rt := htN.1.2.2.2
  have hrh0 : 0 ≤ rh := hhN.1.2.2.2
  have hsmall : P.k * P.δ * P.Q ≤ P.M * P.vbar → P.SO rt ≥ P.SO rh ∧ P.EO rt ≥ P.EO rh := by
    intro hm
    have hmN : N.δ ≤ 2 * N.a * N.b := P.market_bridge.mp hm
    have hb : rh ≤ rt := by rw [hrt, hrh]; exact N.bonusNo_le_bonusAdd hmN
    exact ⟨P.SO_mono hrh0 hb, P.EO_mono hb⟩
  refine ⟨hsmall, ?_, ?_⟩
  · intro hm hp hpH
    have hmN : 2 * N.a * N.b < N.δ := P.market_strict_bridge.mp hm
    have hpN : N.p * N.C < N.v := P.pHat_condition_bridge.mp hpH
    have hb : rt < rh := by rw [hrt, hrh]; exact N.bonusAdd_lt_bonusNo hmN hp hpN
    exact ⟨P.SO_strict hrt0 hb, P.EO_mono (le_of_lt hb), fun hc => P.EO_strict hc hb⟩
  · intro hp hpv
    constructor
    · intro hSE
      have hb : rh ≤ rt := by
        by_contra hn
        have hlt : rt < rh := lt_of_not_ge hn
        have hS := P.SO_strict hrt0 hlt
        linarith [hSE.1]
      have hbN : N.bonusNo ≤ N.bonusAdd := by simpa only [hrt, hrh] using hb
      exact P.market_bridge.mpr ((N.bonusNo_le_bonusAdd_iff hp hpv).mp hbN)
    · exact hsmall

#print axioms solution
