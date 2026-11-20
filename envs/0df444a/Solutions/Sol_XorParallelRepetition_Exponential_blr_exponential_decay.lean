-- Prove2me | solution 1 for XorParallelRepetition.Exponential.blr_exponential_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:42:25.739743+00:00
-- url     : https://prove2.me/submissions/e95b29be-4ff6-4830-817e-8b25da6e76b4

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_Games
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_BLR
import Definitions.Def_XorParallelRepetition_Exponential_Embedding
import Definitions.Def_XorParallelRepetition_Exponential_Contradiction
import Theorems.Thm_XorParallelRepetition_Exponential_blr_no_commuting_embedding
import Theorems.Thm_XorParallelRepetition_Exponential_no_embedding_iff_ordered_contradiction
import Theorems.Thm_XorParallelRepetition_Exponential_tensorized_correlation_decay
universe u

section
set_option autoImplicit false

open scoped ENNReal

namespace XorParallelRepetition.Dev.BlrDecay

open XorParallelRepetition.Exponential


section Sums

variable {α : Type*}

theorem summable_pmf_mul (μ : PMF α) (F : α → ℂ) (C : ℝ) (hF : ∀ a, ‖F a‖ ≤ C) :
    Summable fun a => ((μ a).toReal : ℂ) * F a := by
  refine Summable.of_norm_bounded
    ((ENNReal.summable_toReal μ.tsum_coe_ne_top).mul_left C) fun a => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_comm]
  exact mul_le_mul_of_nonneg_right (hF a) ENNReal.toReal_nonneg

theorem expect_finset_sum {κ : Type*} (μ : PMF α) (s : Finset κ) (G : κ → α → ℂ) (C : ℝ)
    (hG : ∀ c a, ‖G c a‖ ≤ C) :
    expect μ (fun a => ∑ c ∈ s, G c a) = ∑ c ∈ s, expect μ (G c) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum fun c _ => summable_pmf_mul μ (G c) C (hG c)

theorem expect_const_mul (μ : PMF α) (F : α → ℂ) (c : ℂ) :
    expect μ (fun a => c * F a) = c * expect μ F := by
  unfold expect
  rw [← tsum_mul_left]
  congr 1
  funext a
  ring

theorem expect_indicator (μ : PMF α) (E : Set α) [DecidablePred (· ∈ E)] :
    expect μ (fun a => if a ∈ E then 1 else 0) = ((μ.toOuterMeasure E).toReal : ℂ) := by
  unfold expect
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq, Complex.ofReal_tsum]
  · congr 1
    funext a
    by_cases h : a ∈ E <;> simp [h, Set.indicator]
  · intro a
    exact ne_top_of_le_ne_top (PMF.apply_ne_top μ a) (Set.indicator_le_self _ _ a)

theorem winProb_le_one {ι : Type} (G : Game ι) (S : G.Strategy) : G.winProb S ≤ 1 := by
  unfold Game.winProb
  calc G.law.toOuterMeasure _ ≤ G.law.toOuterMeasure Set.univ :=
        PMF.toOuterMeasure_mono _ (fun _ _ => trivial)
    _ = 1 := by rw [PMF.toOuterMeasure_apply_eq_one_iff]; exact Set.subset_univ _

end Sums

section Phase

variable {p : ℕ} [hp : Fact p.Prime]

theorem omega_prim : IsPrimitiveRoot (omega p) p :=
  Complex.isPrimitiveRoot_exp p hp.out.ne_zero

theorem norm_phase (x : ZMod p) : ‖phase p x‖ = 1 := by
  unfold phase
  rw [norm_pow, omega_prim.norm'_eq_one hp.out.ne_zero, one_pow]

theorem phase_add (x y : ZMod p) : phase p (x + y) = phase p x * phase p y := by
  unfold phase
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) p, pow_add, pow_mul,
    omega_prim.pow_eq_one, one_pow, mul_one]

theorem phase_zero : phase p 0 = 1 := by
  unfold phase
  rw [ZMod.val_zero, pow_zero]

theorem phase_inj {x y : ZMod p} (h : phase p x = phase p y) : x = y :=
  ZMod.val_injective p (omega_prim.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)

theorem phase_sum {κ : Type*} [DecidableEq κ] (s : Finset κ) (g : κ → ZMod p) :
    phase p (∑ q ∈ s, g q) = ∏ q ∈ s, phase p (g q) := by
  refine Finset.induction_on s ?_ ?_
  · simp [phase_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, phase_add, ih]

theorem norm_prod_phase {κ : Type*} (s : Finset κ) (g : κ → ZMod p) :
    ‖∏ q ∈ s, phase p (g q)‖ = 1 := by
  rw [norm_prod]
  simp [norm_phase]

/-- Orthogonality of the additive characters of `F_p`. -/
theorem sum_phase_mul (u : ZMod p) :
    ∑ c : ZMod p, phase p (c * u) = if u = 0 then (p : ℂ) else 0 := by
  split_ifs with hu
  · subst hu
    simp [phase_zero, ZMod.card]
  · have h1 : (∑ c : ZMod p, phase p (c * u)) * phase p u = ∑ c : ZMod p, phase p (c * u) := by
      rw [Finset.sum_mul]
      simp_rw [← phase_add]
      have : ∀ c : ZMod p, c * u + u = (c + 1) * u := fun c => by ring
      simp_rw [this]
      exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun c => rfl)
    have h2 : phase p u ≠ 1 := fun h => hu (phase_inj (h.trans phase_zero.symm))
    have h3 : (∑ c : ZMod p, phase p (c * u)) * (phase p u - 1) = 0 := by
      rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) h2

/-- The indicator of `u = 0` in `F_p^n` as an average of characters. -/
theorem indicator_eq {n : ℕ} (u : Fin n → ZMod p) :
    (if ∀ j, u j = 0 then (1 : ℂ) else 0) =
      ((p : ℂ) ^ n)⁻¹ * ∑ c : Fin n → ZMod p, ∏ j, phase p (c j * u j) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  rw [← Fintype.prod_sum (fun j (a : ZMod p) => phase p (a * u j))]
  simp_rw [sum_phase_mul]
  have h1 : ∀ j, (if u j = 0 then (p : ℂ) else 0) = (p : ℂ) * (if u j = 0 then 1 else 0) := by
    intro j
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    inv_mul_cancel_left₀ (pow_ne_zero _ hp0)]
  by_cases h : ∀ j, u j = 0
  · rw [if_pos h]
    exact (Finset.prod_eq_one fun j _ => if_pos (h j)).symm
  · rw [if_neg h]
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)).symm

/-- `∑_c r^{#{j : c_j ≠ 0}} = (1 + (p - 1) r)^n`. -/
theorem sum_weight (n : ℕ) (r : ℝ) :
    ∑ c : Fin n → ZMod p, r ^ (Finset.univ.filter fun j => c j ≠ 0).card =
      (1 + ((p : ℝ) - 1) * r) ^ n := by
  have h1 : ∀ c : Fin n → ZMod p, r ^ (Finset.univ.filter fun j => c j ≠ 0).card =
      ∏ j, (if c j = 0 then 1 else r) := by
    intro c
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun _ (a : ZMod p) => if a = 0 then (1 : ℝ) else r)]
  rw [← Fin.prod_const n (1 + ((p : ℝ) - 1) * r)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h2 : ∀ a : ZMod p, (if a = 0 then (1 : ℝ) else r) = r + (if a = 0 then 1 - r else 0) := by
    intro a
    split_ifs <;> ring
  simp_rw [h2]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, nsmul_eq_mul]
  ring

end Phase

section Bound

variable {p : ℕ} [hp : Fact p.Prime]

/-- The Fourier bound: correlation decay with rate `r` per nonzero coordinate gives
`val(Φ^{⊗n}) ≤ ((1 + (p - 1) r) / p)^n`. -/
theorem repVal_le {κ : Type} [Fintype κ] [DecidableEq κ] (Φ : GeneralizedXorGame.{u} p κ)
    (r : ℝ) (hr0 : 0 ≤ r)
    (hdec : ∀ (n : ℕ) (c : Fin n → ZMod p) (f : ∀ i, (Fin n → Φ.Q i) → ℂ),
      (∀ i x, ‖f i x‖ ≤ 1) →
        ‖expect (iidPMF Φ.μ n) fun s =>
          (∏ i, f i fun j => (s j).1 i) * ∏ j, phase p (c j * (s j).2)‖ ≤
          r ^ (Finset.univ.filter fun j => c j ≠ 0).card)
    (n : ℕ) : Φ.repVal n ≤ ((1 + ((p : ℝ) - 1) * r) / p) ^ n := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hB : 0 ≤ ((1 + ((p : ℝ) - 1) * r) / p) ^ n :=
    pow_nonneg (div_nonneg (by nlinarith) (by linarith)) n
  unfold GeneralizedXorGame.repVal Game.val
  apply ENNReal.toReal_le_of_le_ofReal hB
  refine iSup_le fun A => ?_
  have hfin : (Φ.toGame.rep n).winProb A ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (winProb_le_one _ _)
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  let A' : ∀ i, (Fin n → Φ.Q i) → Fin n → ZMod p := A
  let E : Set (Fin n → (∀ i, Φ.Q i) × ZMod p) :=
    {s | ∀ j, ∑ i, A' i (fun j => (s j).1 i) j = (s j).2}
  have e2 : (Φ.toGame.rep n).winProb A = (iidPMF Φ.μ n).toOuterMeasure E := by
    unfold Game.winProb
    exact PMF.toOuterMeasure_map_apply _ _ _
  let uu : (Fin n → (∀ i, Φ.Q i) × ZMod p) → Fin n → ZMod p :=
    fun s j => ∑ i, A' i (fun j => (s j).1 i) j - (s j).2
  let G : (Fin n → ZMod p) → (Fin n → (∀ i, Φ.Q i) × ZMod p) → ℂ :=
    fun c s => ∏ j, phase p (c j * uu s j)
  have hGn : ∀ c s, ‖G c s‖ ≤ 1 := fun c s => le_of_eq (norm_prod_phase _ _)
  classical
  have hind : ∀ s, (if s ∈ E then (1 : ℂ) else 0) = ((p : ℂ) ^ n)⁻¹ * ∑ c, G c s := by
    intro s
    rw [← indicator_eq]
    have hiff : s ∈ E ↔ ∀ j, uu s j = 0 := by
      simp only [E, uu, Set.mem_ofPred_eq, sub_eq_zero]
    by_cases h : s ∈ E
    · rw [if_pos h, if_pos (hiff.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]
  have hexp : (((iidPMF Φ.μ n).toOuterMeasure E).toReal : ℂ) =
      ((p : ℂ) ^ n)⁻¹ * ∑ c, expect (iidPMF Φ.μ n) (G c) := by
    rw [← expect_indicator]
    simp_rw [hind]
    rw [expect_const_mul, expect_finset_sum _ _ _ 1 hGn]
  have hG : ∀ c, ‖expect (iidPMF Φ.μ n) (G c)‖ ≤
      r ^ (Finset.univ.filter fun j => c j ≠ 0).card := by
    intro c
    have h := hdec n (-c) (fun i x => ∏ j, phase p (c j * A' i x j))
      (fun i x => le_of_eq (norm_prod_phase _ _))
    have hcard : (Finset.univ.filter fun j => (-c) j ≠ 0) =
        (Finset.univ.filter fun j => c j ≠ 0) := by
      simp only [Pi.neg_apply, ne_eq, neg_eq_zero]
    rw [hcard] at h
    refine le_of_eq_of_le ?_ h
    congr 2
    funext s
    simp only [G, uu]
    rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← phase_sum, ← phase_add, Pi.neg_apply]
    congr 1
    rw [mul_sub, Finset.mul_sum]
    ring
  rw [e2]
  have hp0 : (0 : ℝ) < (p : ℝ) ^ n := pow_pos (by linarith) n
  calc ((iidPMF Φ.μ n).toOuterMeasure E).toReal
      = ‖((((iidPMF Φ.μ n).toOuterMeasure E).toReal : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    _ = ((p : ℝ) ^ n)⁻¹ * ‖∑ c, expect (iidPMF Φ.μ n) (G c)‖ := by
        rw [hexp, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    _ ≤ ((p : ℝ) ^ n)⁻¹ * ∑ c : Fin n → ZMod p, r ^ (Finset.univ.filter fun j => c j ≠ 0).card :=
        mul_le_mul_of_nonneg_left
          ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hG c))
          (inv_nonneg.2 hp0.le)
    _ = ((1 + ((p : ℝ) - 1) * r) / p) ^ n := by
        rw [sum_weight, div_pow, inv_mul_eq_div]

end Bound

section Support

variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem blr_mem_support (Ψ : XorGame.{u} p ι) (x : ∀ i, Ψ.Q i) (hx : x ∈ Ψ.μ.support)
    (γ : ZMod p) (α : ι → ZMod p) : Ψ.blrChallenge x γ α ∈ Ψ.blr.μ.support := by
  exact (PMF.mem_support_bind_iff _ _ _).2 ⟨x, hx, (PMF.mem_support_bind_iff _ _ _).2
    ⟨γ, PMF.mem_support_uniformOfFintype _, (PMF.mem_support_map_iff _ _ _).2
      ⟨α, PMF.mem_support_uniformOfFintype _, rfl⟩⟩⟩

omit [DecidableEq ι] in
theorem exists_t_ne_zero (Ψ : XorGame.{u} p ι) (hval : Ψ.val < 1) :
    ∃ x ∈ Ψ.μ.support, Ψ.t x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine absurd ?_ (not_le.2 hval)
  unfold XorGame.val GeneralizedXorGame.val Game.val
  let S : Ψ.toGeneralized.toGame.Strategy := fun _ _ => (0 : ZMod p)
  have hS : Ψ.toGeneralized.toGame.winProb S = 1 := by
    unfold Game.winProb
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro ω hω
    have hω' : ω ∈ (Ψ.μ.map fun x => (x, Ψ.t x)).support := hω
    rw [PMF.support_map] at hω'
    obtain ⟨x, hx, rfl⟩ := hω'
    show ∑ _i, (0 : ZMod p) = Ψ.t x
    rw [Finset.sum_const_zero]
    exact (hcon x hx).symm
  have hsup : (⨆ S, Ψ.toGeneralized.toGame.winProb S) = 1 :=
    le_antisymm (iSup_le fun S => winProb_le_one _ S) (hS ▸ le_iSup _ S)
  rw [hsup, ENNReal.toReal_one]

end Support

end XorParallelRepetition.Dev.BlrDecay

namespace XorParallelRepetition.Exponential


open XorParallelRepetition.Dev.BlrDecay in
theorem chk_blr_exponential_decay {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : XorGame.{u} p ι) (hval : Ψ.val < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, Ψ.blr.repVal n ≤ (1 - ε) ^ n := by
  obtain ⟨N, hN⟩ :=
    (no_embedding_iff_ordered_contradiction Ψ.blr).1 (blr_no_commuting_embedding Ψ hval)
  obtain ⟨x, hx, htx⟩ := exists_t_ne_zero Ψ hval
  have hnd : Nonempty (ι × Bool) ∨ Ψ.blr.HasTwoTargets :=
    Or.inr ⟨_, blr_mem_support Ψ x hx 0 0, _, blr_mem_support Ψ x hx 1 0,
      by simpa [XorGame.blrChallenge] using htx.symm⟩
  obtain ⟨ε₀, hε₀, hdec0⟩ := tensorized_correlation_decay Ψ.blr N hN hnd
  set r : ℝ := max (1 - ε₀) 0 with hr
  have hr0 : 0 ≤ r := le_max_right _ _
  have hr1 : r < 1 := max_lt (by linarith) one_pos
  have hdec : ∀ (n : ℕ) (c : Fin n → ZMod p) (f : ∀ i, (Fin n → Ψ.blr.Q i) → ℂ),
      (∀ i x, ‖f i x‖ ≤ 1) →
        ‖expect (iidPMF Ψ.blr.μ n) fun s =>
          (∏ i, f i fun j => (s j).1 i) * ∏ j, phase p (c j * (s j).2)‖ ≤
          r ^ (Finset.univ.filter fun j => c j ≠ 0).card := by
    intro n c f hf
    by_cases h : 0 ≤ 1 - ε₀
    · rw [hr, max_eq_left h]
      exact hdec0 n _ c le_rfl f hf
    · rw [hr, max_eq_right (le_of_not_ge h)]
      rcases Nat.eq_zero_or_pos (Finset.univ.filter fun j => c j ≠ 0).card with hk | hk
      · rw [hk, pow_zero]
        simpa using hdec0 n 0 c (Nat.zero_le _) f hf
      · have h1 := hdec0 n 1 c hk f hf
        rw [pow_one] at h1
        exact absurd (lt_of_le_of_lt (norm_nonneg _) (h1.trans_lt (lt_of_not_ge h))) (lt_irrefl 0)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine ⟨((p : ℝ) - 1) * (1 - r) / p, by
    apply div_pos (mul_pos (by linarith) (by linarith)) (by linarith), fun n => ?_⟩
  have h := repVal_le Ψ.blr r hr0 hdec n
  have he : (1 + ((p : ℝ) - 1) * r) / p = 1 - ((p : ℝ) - 1) * (1 - r) / p := by
    field_simp
    ring
  rwa [he] at h

end XorParallelRepetition.Exponential
end

theorem solution : type_of% @XorParallelRepetition.Exponential.chk_blr_exponential_decay := @XorParallelRepetition.Exponential.chk_blr_exponential_decay
