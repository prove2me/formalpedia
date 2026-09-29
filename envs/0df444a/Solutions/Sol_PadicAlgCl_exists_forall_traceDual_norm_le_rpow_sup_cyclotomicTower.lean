-- Prove2me | solution 1 for PadicAlgCl.exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/35a920e1-f235-5c24-82d6-38a271966181

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Theorems.Thm_PadicAlgCl_exists_forall_exists_polynomial_aeval_eq_of_norm_le_one
import Theorems.Thm_PadicAlgCl_norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one
import Theorems.Thm_PadicAlgCl_exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open scoped Classical

namespace TWA

open Polynomial IntermediateField

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Q" => PadicAlgCl.cyclotomicTower p

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

lemma norm_natCast_p : ‖(p : Ω)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω) p, norm_algebraMap', Padic.norm_p]

private lemma _root_.TWA.exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ n) := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero ((p ^ n : ℕ) : Ω) := ⟨by exact_mod_cast hne⟩
  haveI : IsCyclotomicExtension {p ^ n} Ω Ω := IsSepClosedOfCharZero.isCyclotomicExtension _ _
  exact IsCyclotomicExtension.exists_isPrimitiveRoot Ω Ω (S := {p ^ n}) rfl hne

p2m_export "TWA" "exists_isPrimitiveRoot"
lemma cyclotomicTower_eq_adjoin (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    Q n = IntermediateField.adjoin ℚ_[p] {ζ} := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  apply le_antisymm
  · unfold PadicAlgCl.cyclotomicTower
    rw [IntermediateField.adjoin_le_iff]
    intro ξ (hξ : ξ ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · exact IntermediateField.adjoin.mono ℚ_[p] _ _ (Set.singleton_subset_iff.mpr hζ.pow_eq_one)

scoped instance finiteDimensional_Q (n : ℕ) : FiniteDimensional ℚ_[p] (Q n) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p n
  rw [cyclotomicTower_eq_adjoin p n hζ]
  exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)

lemma exists_norm_pow_mul_le_one (z : Ω) : ∃ k : ℕ, ‖(p : Ω) ^ k * z‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖z‖ (one_lt_p p)
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_pow, norm_natCast_p, inv_pow]
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (p_pos p) k
  calc ((p : ℝ) ^ k)⁻¹ * ‖z‖ ≤ ((p : ℝ) ^ k)⁻¹ * (p : ℝ) ^ k := by gcongr
    _ = 1 := inv_mul_cancel₀ hpk.ne'

lemma pow_card_le_norm_prod (a : Ω) {c : ℝ} (hc : 0 ≤ c) (s : Multiset Ω)
    (hs : ∀ b ∈ s, c ≤ ‖a - b‖) : c ^ s.card ≤ ‖(s.map fun b => a - b).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, pow_succ, mul_comm]
    exact mul_le_mul (hs b (Multiset.mem_cons_self b s))
      (ih fun b' hb' => hs b' (Multiset.mem_cons_of_mem hb')) (pow_nonneg hc _) (norm_nonneg _)

section Degree

variable {M F : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] M]
  [FiniteDimensional ℚ_[p] F]

lemma finrank_extendScalars_pos :
    0 < Module.finrank F (extendScalars (F := F) (E := M ⊔ F) le_sup_right) := by
  rw [← relfinrank_eq_finrank_of_le]
  have h := finrank_bot_mul_relfinrank (le_sup_right : F ≤ M ⊔ F)
  have hpos : 0 < Module.finrank ℚ_[p] (M ⊔ F : IntermediateField ℚ_[p] Ω) := Module.finrank_pos
  by_contra h0
  rw [not_lt, Nat.le_zero] at h0
  rw [h0, mul_zero] at h
  omega

lemma finrank_extendScalars_le :
    Module.finrank F (extendScalars (F := F) (E := M ⊔ F) le_sup_right) ≤ Module.finrank ℚ_[p] M := by
  rw [← relfinrank_eq_finrank_of_le]
  have h := finrank_bot_mul_relfinrank (le_sup_right : F ≤ M ⊔ F)
  have hle := IntermediateField.finrank_sup_le M F
  have hFpos : 0 < Module.finrank ℚ_[p] F := Module.finrank_pos
  have h2 : Module.finrank ℚ_[p] F * relfinrank F (M ⊔ F) ≤
      Module.finrank ℚ_[p] F * Module.finrank ℚ_[p] M := by
    rw [h, mul_comm]; exact hle
  exact Nat.le_of_mul_le_mul_left h2 hFpos

scoped instance finite_extendScalars :
    Module.Finite F (extendScalars (F := F) (E := M ⊔ F) le_sup_right) :=
  Module.finite_of_finrank_pos (finrank_extendScalars_pos p)

end Degree

abbrev EE (M F : IntermediateField ℚ_[p] (PadicAlgCl p)) : IntermediateField F (PadicAlgCl p) :=
  extendScalars (F := F) (E := M ⊔ F) le_sup_right

theorem layer_bound (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M]
    (M' : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ)
    (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F]
    (hFQ : Q n ≤ F) (hEM' : M ⊔ F ≤ M' ⊔ Q n) {ε : ℝ} (hε : 0 < ε)
    (hT : ∀ a : Ω, a ∈ M' ⊔ Q n → ‖a‖ ≤ 1 → Q n ≤ IntermediateField.adjoin ℚ_[p] {a} →
      (∀ c ∈ IntermediateField.adjoin ℚ_[p] {a}, ‖c‖ ≤ 1 →
        ∃ P : ℚ_[p][X], (∀ i, ‖P.coeff i‖ ≤ 1) ∧ aeval a P = c) →
      ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (Q n).fixingSubgroup → σ a ≠ a →
        (p : ℝ) ^ (-(ε / Module.finrank ℚ_[p] M)) < ‖σ a - a‖)
    (z : EE p M F)
    (hz : ∀ w : EE p M F, ‖(w : Ω)‖ ≤ 1 →
      ‖((Algebra.trace F (EE p M F) (z * w) : F) : Ω)‖ ≤ 1) :
    ‖(z : Ω)‖ ≤ (p : ℝ) ^ ε := by
  set d : ℕ := Module.finrank ℚ_[p] M with hddef
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1

  obtain ⟨α, hα1, hαtop, hαgen⟩ :=
    PadicAlgCl.exists_forall_exists_polynomial_aeval_eq_of_norm_le_one p F (EE p M F)
  have hB8 := PadicAlgCl.norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one
    p F (EE p M F) hα1 hαtop z hz
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hfirr : Irreducible (minpoly F α) := minpoly.irreducible hint
  have hfmonic : (minpoly F α).Monic := minpoly.monic hint
  set fΩ : Polynomial (PadicAlgCl p) := (minpoly F α).map (algebraMap F Ω) with hfΩdef
  have hfΩmonic : fΩ.Monic := hfmonic.map _
  have hfΩsep : fΩ.Separable := hfirr.separable.map
  have hcoe_aeval : ∀ P : F[X], ((aeval α P : EE p M F) : Ω) = aeval (α : Ω) P := by
    intro P
    have h := aeval_algHom_apply (EE p M F).val α P
    exact h.symm
  have hcoe_aevalQ : ∀ P : ℚ_[p][X], ((aeval α P : EE p M F) : Ω) = aeval (α : Ω) P := by
    intro P
    have h := aeval_algHom_apply ((EE p M F).val.restrictScalars ℚ_[p]) α P
    exact h.symm
  have hfa : aeval (α : Ω) (minpoly F α) = 0 := by rw [← hcoe_aeval, minpoly.aeval]; rfl
  have hamem : (α : Ω) ∈ fΩ.roots := by
    rw [mem_roots hfΩmonic.ne_zero, IsRoot.def, hfΩdef, eval_map_algebraMap, hfa]
  have hderiv : aeval (α : Ω) (derivative (minpoly F α)) =
      ((fΩ.roots.erase (α : Ω)).map fun b => (α : Ω) - b).prod := by
    rw [← Splits.eval_root_derivative (IsAlgClosed.splits fΩ) hfΩmonic hamem, hfΩdef,
      derivative_map, eval_map_algebraMap]
  have hB8' : ‖(z : Ω)‖ * ‖aeval (α : Ω) (derivative (minpoly F α))‖ ≤ 1 := by
    rw [← hcoe_aeval, ← norm_mul, ← MulMemClass.coe_mul]
    exact hB8

  have hEle : (M ⊔ F : IntermediateField ℚ_[p] Ω) ≤ IntermediateField.adjoin ℚ_[p] {(α : Ω)} := by
    intro ω hω
    obtain ⟨k, hk⟩ := exists_norm_pow_mul_le_one p ω
    set ωE : EE p M F := ⟨ω, hω⟩ with hωE
    have hk' : ‖(((p : EE p M F) ^ k * ωE : EE p M F) : Ω)‖ ≤ 1 := by push_cast; exact hk
    obtain ⟨P, -, hP⟩ := hαgen _ hk'
    have hmem : (p : Ω) ^ k * ω ∈ IntermediateField.adjoin ℚ_[p] {(α : Ω)} := by
      have h1 : (p : Ω) ^ k * ω = aeval (α : Ω) P := by
        rw [← hcoe_aevalQ, hP]; push_cast; rfl
      rw [h1]
      exact (IntermediateField.algebra_adjoin_le_adjoin ℚ_[p] {(α : Ω)})
        (Polynomial.aeval_mem_adjoin_singleton ℚ_[p] (α : Ω))
    have hpk : ((p : Ω) ^ k) ≠ 0 := pow_ne_zero k (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have hω' : ω = ((p : Ω) ^ k)⁻¹ * ((p : Ω) ^ k * ω) := by
      rw [← mul_assoc, inv_mul_cancel₀ hpk, one_mul]
    rw [hω']
    refine IntermediateField.mul_mem _ (IntermediateField.inv_mem _ ?_) hmem
    exact pow_mem (IntermediateField.natCast_mem _ p) k
  have hQa : Q n ≤ IntermediateField.adjoin ℚ_[p] {(α : Ω)} :=
    (hFQ.trans le_sup_right).trans hEle
  have haM' : (α : Ω) ∈ M' ⊔ Q n := hEM' α.2
  have hgen : ∀ c ∈ IntermediateField.adjoin ℚ_[p] {(α : Ω)}, ‖c‖ ≤ 1 →
      ∃ P : ℚ_[p][X], (∀ i, ‖P.coeff i‖ ≤ 1) ∧ aeval (α : Ω) P = c := by
    intro c hc hc1
    have hcE : c ∈ (M ⊔ F : IntermediateField ℚ_[p] Ω) := by
      have hle : IntermediateField.adjoin ℚ_[p] {(α : Ω)} ≤ M ⊔ F :=
        IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr α.2)
      exact hle hc
    obtain ⟨P, hP, hPc⟩ := hαgen ⟨c, hcE⟩ hc1
    exact ⟨P, hP, by rw [← hcoe_aevalQ, hPc]⟩

  set c₀ : ℝ := (p : ℝ) ^ (-(ε / d)) with hc₀
  have hc₀pos : 0 < c₀ := Real.rpow_pos_of_pos (p_pos p) _
  have hc₀1 : c₀ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (one_lt_p p).le (by
    have := div_pos hε hdpos; linarith)
  have hroots : ∀ b ∈ fΩ.roots.erase (α : Ω), c₀ ≤ ‖(α : Ω) - b‖ := by
    intro b hb
    rw [(nodup_roots hfΩsep).mem_erase_iff] at hb
    obtain ⟨hba, hb⟩ := hb
    have hfb : aeval b (minpoly F α) = 0 := by
      rw [mem_roots hfΩmonic.ne_zero, IsRoot.def, hfΩdef, eval_map_algebraMap] at hb
      exact hb
    have hmin : minpoly F b = minpoly F (α : Ω) := by
      rw [show ((α : EE p M F) : Ω) = (EE p M F).val α from rfl,
        minpoly.algHom_eq (EE p M F).val (EE p M F).val.injective α]
      exact (minpoly.eq_of_irreducible_of_monic hfirr hfb hfmonic).symm
    obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).mp hmin
    have hσfix : τ.restrictScalars ℚ_[p] ∈ (Q n).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro q hq
      rw [AlgEquiv.restrictScalars_apply]
      exact τ.commutes (⟨q, hFQ hq⟩ : F)
    have hσa : τ.restrictScalars ℚ_[p] (α : Ω) = b := by
      rw [AlgEquiv.restrictScalars_apply]; exact hτ
    have hne : τ.restrictScalars ℚ_[p] (α : Ω) ≠ (α : Ω) := by rw [hσa]; exact hba
    have h := hT (α : Ω) haM' hα1 hQa hgen _ hσfix hne
    rw [hσa, norm_sub_rev] at h
    exact h.le

  have hcard : (fΩ.roots.erase (α : Ω)).card ≤ d := by
    rw [Multiset.card_erase_of_mem hamem]
    refine (Nat.pred_le _).trans ?_
    calc fΩ.roots.card ≤ fΩ.natDegree := card_roots' _
      _ = (minpoly F α).natDegree := hfmonic.natDegree_map _
      _ ≤ Module.finrank F (EE p M F) := minpoly.natDegree_le α
      _ ≤ d := finrank_extendScalars_le p
  have hlow : (p : ℝ) ^ (-ε) ≤ ‖aeval (α : Ω) (derivative (minpoly F α))‖ := by
    calc (p : ℝ) ^ (-ε) = c₀ ^ d := by
          rw [hc₀, ← Real.rpow_natCast, ← Real.rpow_mul (p_pos p).le]
          congr 1
          field_simp
      _ ≤ c₀ ^ (fΩ.roots.erase (α : Ω)).card := pow_le_pow_of_le_one hc₀pos.le hc₀1 hcard
      _ ≤ ‖((fΩ.roots.erase (α : Ω)).map fun b => (α : Ω) - b).prod‖ :=
          pow_card_le_norm_prod p (α : Ω) hc₀pos.le _ hroots
      _ = ‖aeval (α : Ω) (derivative (minpoly F α))‖ := by rw [hderiv]
  have hpos : 0 < (p : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (p_pos p) _
  have hdpos' : 0 < ‖aeval (α : Ω) (derivative (minpoly F α))‖ := hpos.trans_le hlow
  calc ‖(z : Ω)‖ = ‖(z : Ω)‖ * ‖aeval (α : Ω) (derivative (minpoly F α))‖ /
        ‖aeval (α : Ω) (derivative (minpoly F α))‖ := by
        field_simp
    _ ≤ 1 / (p : ℝ) ^ (-ε) := by gcongr
    _ = (p : ℝ) ^ ε := by rw [Real.rpow_neg (p_pos p).le, one_div, inv_inv]

theorem main (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ z : IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
          (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right,
        (∀ w : IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
            (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right,
          ‖(w : PadicAlgCl p)‖ ≤ 1 →
          ‖((Algebra.trace ↥(K ⊔ PadicAlgCl.cyclotomicTower p n)
              ↥(IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
                (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right) (z * w) :
                ↥(K ⊔ PadicAlgCl.cyclotomicTower p n)) : PadicAlgCl p)‖ ≤ 1) →
        ‖(z : PadicAlgCl p)‖ ≤ (p : ℝ) ^ ε := by

  set M' : IntermediateField ℚ_[p] Ω := IntermediateField.normalClosure ℚ_[p] ↥(M ⊔ K) Ω
    with hM'
  haveI : FiniteDimensional ℚ_[p] M' := normalClosure.is_finiteDimensional ℚ_[p] ↥(M ⊔ K) Ω
  haveI : Normal ℚ_[p] M' := normalClosure.normal ℚ_[p] ↥(M ⊔ K) Ω
  have hMK : M ⊔ K ≤ M' := IntermediateField.le_normalClosure (M ⊔ K)
  have hdpos : (0 : ℝ) < Module.finrank ℚ_[p] M := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ_[p] M)
  obtain ⟨N, hN⟩ :=
    PadicAlgCl.exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower p M'
      (ε / Module.finrank ℚ_[p] M) (div_pos hε hdpos)
  refine ⟨N, fun n hn z hz => ?_⟩
  have hFQ : Q n ≤ K ⊔ Q n := le_sup_right
  have hEM' : M ⊔ (K ⊔ Q n) ≤ M' ⊔ Q n := by
    refine sup_le ((le_sup_left.trans hMK).trans le_sup_left) (sup_le ?_ le_sup_right)
    exact (le_sup_right.trans hMK).trans le_sup_left
  exact layer_bound p M M' n (K ⊔ Q n) hFQ hEM' hε (hN n hn) z hz

end TWA
p2m_reactivate "P2MW.S_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower.TWA"

end
p2m_reactivate "P2MW.S_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower.TWA"

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ z : IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
          (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right,
        (∀ w : IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
            (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right,
          ‖(w : PadicAlgCl p)‖ ≤ 1 →
          ‖((Algebra.trace ↥(K ⊔ PadicAlgCl.cyclotomicTower p n)
              ↥(IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
                (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right) (z * w) :
                ↥(K ⊔ PadicAlgCl.cyclotomicTower p n)) : PadicAlgCl p)‖ ≤ 1) →
        ‖(z : PadicAlgCl p)‖ ≤ (p : ℝ) ^ ε :=
  TWA.main p K M ε hε

end S_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower
end P2MW
export P2MW.S_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower (solution)
