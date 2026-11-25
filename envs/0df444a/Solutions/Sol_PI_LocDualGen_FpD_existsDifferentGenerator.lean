-- Prove2me | solution 1 for PI.LocDualGen.FpD.existsDifferentGenerator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:04:36.675622+00:00
-- url     : https://prove2.me/submissions/f181a7ba-e34e-4035-af83-dac2d8c74fbb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDual
import Theorems.Thm_PI_LocDualGen_FpD_exists_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open ValuativeRel
namespace PI.LocDualGen.FpD
open PI.LocDualGen.W
section
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
private theorem isOpen_lemma_2 : IsOpen (𝒪[K] : Set K) := by
  have h0 : ((𝒪[K]).toAddSubgroup : Set K) ∈ nhds (0 : K) := by
    refine (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun z hz => ?_⟩
    have hz' : ValuativeRel.valuation K z < 1 := by simpa using hz
    exact (Valuation.mem_integer_iff _ _).2 hz'.le
  exact AddSubgroup.isOpen_of_mem_nhds _ h0
private theorem int_lemma_4 (hcont : Continuous (algebraMap ℚ_[l] K)) (z : ℚ_[l]) (hz : ‖z‖ ≤ 1) :
    algebraMap ℚ_[l] K z ∈ 𝒪[K] := by
  have hcl : IsClosed (𝒪[K] : Set K) :=
    AddSubgroup.isClosed_of_isOpen ((𝒪[K]).toAddSubgroup) (isOpen_lemma_2 (K := K))
  let w : ℤ_[l] := ⟨z, hz⟩
  have key : algebraMap ℚ_[l] K (w : ℚ_[l]) ∈ 𝒪[K] := by
    refine PadicInt.denseRange_natCast.induction_on w ?_ ?_
    · exact hcl.preimage (hcont.comp continuous_subtype_val)
    · intro n
      rw [PadicInt.coe_natCast, map_natCast]
      exact natCast_mem _ n

  exact key
private theorem small_lemma_5 (hcont : Continuous (algebraMap ℚ_[l] K)) (y : K) :
    ∃ N : ℕ, ∀ k ≥ N, algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ k) * y ∈ 𝒪[K] := by
  have h1 : Filter.Tendsto (fun k : ℕ => (l : ℚ_[l]) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by first
      | exact Padic.norm_p_lt_one
      | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))
  have h2 : Filter.Tendsto (fun k : ℕ => algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ k) * y)
      Filter.atTop (nhds 0) := by
    have := ((hcont.tendsto 0).comp h1).mul_const y
    rw [map_zero, zero_mul] at this
    exact this
  have h3 : (𝒪[K] : Set K) ∈ nhds (0 : K) := (isOpen_lemma_2 (K := K)).mem_nhds (zero_mem _)
  exact Filter.eventually_atTop.1 (h2.eventually_mem h3)
private theorem P_add_mem {x y : K} (hx : P l x) (hy : P l y) : P l (x + y) := fun b => by
  rw [add_mul, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx b) (hy b))
private theorem mul_mem_dual₂ {x : K} (hx : P l x) (c : 𝒪[K]) : P l (x * c) := fun b => by
  rw [mul_assoc]
  exact hx (c * b)
private theorem bound_lemma_8 (hcont : Continuous (algebraMap ℚ_[l] K)) :
    ∃ m : ℕ, ∀ x : K, P l x → algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ∈ 𝒪[K] := by
  classical
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hnd := traceForm_nondegenerate ℚ_[l] K
  let B := Module.finBasis ℚ_[l] K
  choose N hN using fun i => small_lemma_5 l hcont (B i)
  let b := B.isUnitSMul (w := fun i => (l : ℚ_[l]) ^ N i)
    (fun i => (isUnit_iff_ne_zero.2 hl0).pow _)
  have hb : ∀ i, b i ∈ 𝒪[K] := fun i => by
    simp only [b, Module.Basis.isUnitSMul_apply, Algebra.smul_def]
    exact hN i (N i) le_rfl
  let D := (Algebra.traceForm ℚ_[l] K).dualBasis hnd b
  choose N' hN' using fun i => small_lemma_5 l hcont (D i)
  refine ⟨Finset.univ.sup N', fun x hx => ?_⟩
  have hc : ∀ i, algebraMap ℚ_[l] K (D.repr x i) ∈ 𝒪[K] := fun i => by
    apply int_lemma_4 l hcont
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    exact hx ⟨b i, hb i⟩
  rw [← D.sum_repr x, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, mul_left_comm]
  exact mul_mem (hc i) (hN' i _ (Finset.le_sup (Finset.mem_univ i)))
end
private theorem main_lemma_9 {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (hcont : Continuous (algebraMap ℚ_[l] K)) :
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[K] := by
  classical
  obtain ⟨m, hm⟩ := bound_lemma_8 l hcont
  obtain ⟨x0, hx0, hPx0⟩ := exists_ne_zero l hcont
  set t : K := algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) with ht
  have ht0 : t ≠ 0 := by
    rw [ht, Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  let I : Ideal 𝒪[K] :=
    { carrier := {c | P l ((c : K) * t⁻¹)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        push_cast
        rw [add_mul]
        exact P_add_mem l ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro b
        simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        have h := mul_mem_dual₂ l ha c
        have e : ((c * a : 𝒪[K]) : K) * t⁻¹ = (a : K) * t⁻¹ * (c : K) := by
          push_cast
          ring
        rw [e]
        exact h }
  obtain ⟨g0, hg0⟩ := Submodule.IsPrincipal.principal I
  have hmem : ∀ c : 𝒪[K], c ∈ I ↔ P l ((c : K) * t⁻¹) := fun c => Iff.rfl
  have hspan : ∀ c : 𝒪[K], c ∈ I ↔ ∃ r : 𝒪[K], r * g0 = c := fun c => by
    rw [hg0, Submodule.mem_span_singleton]
    rfl
  have hc0 : (⟨t * x0, hm x0 hPx0⟩ : 𝒪[K]) ∈ I := by
    rw [hmem]
    have e : t * x0 * t⁻¹ = x0 := by field_simp
    simpa only [e] using hPx0
  have hg0I : g0 ∈ I := (hspan g0).2 ⟨1, one_mul _⟩
  have hg0ne : (g0 : K) ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := (hspan _).1 hc0
    have := congrArg (fun u : 𝒪[K] => (u : K)) hr
    simp only [Subring.coe_mul, h, mul_zero] at this
    exact mul_ne_zero ht0 hx0 this.symm
  set g : K := (g0 : K) * t⁻¹ with hg
  have hPg : P l g := (hmem g0).1 hg0I
  have hgne : g ≠ 0 := mul_ne_zero hg0ne (inv_ne_zero ht0)
  refine ⟨g⁻¹, inv_ne_zero hgne, fun a => ?_⟩
  simp only [inv_inv]
  constructor
  · intro h
    have hPa : P l (a * g) := fun b => by
      have e : a * g * (b : K) = a * (b : K) * g := by ring
      rw [e]
      exact h b
    have hc : (⟨t * (a * g), hm _ hPa⟩ : 𝒪[K]) ∈ I := by
      rw [hmem]
      have e : t * (a * g) * t⁻¹ = a * g := by field_simp
      simpa only [e] using hPa
    obtain ⟨r, hr⟩ := (hspan _).1 hc
    have h2 := congrArg (fun u : 𝒪[K] => (u : K)) hr
    simp only [Subring.coe_mul] at h2
    have h3 : (r : K) = a := by
      have e : t * (a * g) = a * (g0 : K) := by
        rw [hg]
        field_simp
      rw [e] at h2
      exact mul_right_cancel₀ hg0ne h2
    rw [← h3]
    exact r.2
  · intro ha b
    have h := mul_mem_dual₂ l hPg ⟨a, ha⟩ b
    have e : a * (b : K) * g = g * a * (b : K) := by ring
    rw [e]
    exact h
end PI.LocDualGen.FpD
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel
open PI PI.LocDualGen PI.LocDualGen.FpD
open PI.LocDualGen.W
namespace PI.LocDualGen.FpD
theorem _root_.solution : FpDual := by
  intro K _ _ _ l _ _ hK _ hcont hfin
  haveI := hK
  haveI := hfin
  exact main_lemma_9 l hcont
end PI.LocDualGen.FpD
