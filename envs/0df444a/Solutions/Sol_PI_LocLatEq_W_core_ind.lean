-- Prove2me | solution 1 for PI.LocLatEq.W.core_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:24.227747+00:00
-- url     : https://prove2.me/submissions/5c154c7b-a996-4535-b550-1891337cea15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreGenIdeal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreFgOfLe
import Theorems.Thm_PI_LocLatEq_W_core_fg_of_le
import Theorems.Thm_PI_LocLatEq_W_core_int_mem
import Theorems.Thm_PI_LocLatEq_W_core_nontriv
import Theorems.Thm_PI_LocLatEq_W_core_bc_sub
import Theorems.Thm_PI_LocLatEq_W_core_smem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_LocLatEq_W_bc_smul
import Theorems.Thm_PI_LocLatEq_W_core_gen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
namespace PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
private theorem ringOfIntegers_smul_eq_coe_mul (r : 𝓞 E) (x : E) : r • x = (r : E) * x :=
  Algebra.smul_def r x
private theorem locLatEq_bc_apply (A : Formalism.MainNotions.S.Loc.LocAt F E sig p) {n : ℕ} (x : Fin n → E)
    (i : Fin n) : PI.LocLatEq.bc A x i = A.ιE (x i) := rfl
private theorem locLatEq_bc_mem_latL_of_mem (A : Formalism.MainNotions.S.Loc.LocAt F E sig p) {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E} (hx : x ∈ Λ) :
    PI.LocLatEq.bc A x ∈ PI.LocLatEq.latL A Λ := by
  unfold PI.LocLatEq.latL
  exact Submodule.subset_span ⟨x, hx, rfl⟩
private theorem mul_not_mem_asIdeal_of_not_mem {d d' : 𝓞 F} (hd : d ∉ p.asIdeal) (hd' : d' ∉ p.asIdeal) :
    d * d' ∉ p.asIdeal := fun h => (p.isPrime.mem_or_mem h).elim hd hd'
private theorem exists_linearMap_eq_cons_zero (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) : ∃ L : (Fin n → M) →ₗ[R] (Fin (n + 1) → M),
      ∀ v, L v = (Fin.cons (0 : M) v : Fin (n + 1) → M) :=
  ⟨{ toFun := fun v => (Fin.cons (0 : M) v : Fin (n + 1) → M)
     map_add' := fun v w => by
       funext i
       cases i using Fin.cases <;> simp
     map_smul' := fun c v => by
       funext i
       cases i using Fin.cases <;> simp }, fun _ => rfl⟩
end PI.LocLatEq.W
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocLatEq PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
set_option maxHeartbeats 800000
namespace PI.LocLatEq.W
theorem _root_.solution (hU : UnitP) (hA : AvoidP) (hI : IntP) (h2 : Module.finrank F E = 2)
    (A : LocAt F E sig p) : ∀ (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG →
    ∀ y : Fin n → E, bc A y ∈ latL A Λ →
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) d • y ∈ Λ := by
  have := core_nontriv A
  intro n
  induction n with
  | zero =>
    intro Λ _ y _
    refine ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    have hy0 : y = 0 := funext fun i => i.elim0
    rw [hy0, smul_zero]
    exact Λ.zero_mem
  | succ n ih =>
    intro Λ hΛ y hy
    obtain ⟨L, hL⟩ := exists_linearMap_eq_cons_zero (𝓞 E) E n
    have hinj : Function.Injective L := fun v w h => funext fun j => by
      simpa [hL] using congrFun h j.succ
    have hmapFG : (Submodule.map L (Λ.comap L)).FG :=
      core_fg_of_le hΛ (Submodule.map_comap_le L Λ)
    have hFG : (Λ.comap L).FG := Submodule.fg_of_fg_map_injective L hinj hmapFG
    obtain ⟨a, haI, hgen⟩ := core_gen hA p
      (Λ.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin (n + 1) => E) 0)) (hΛ.map _)
    have hx0 : ∀ x ∈ Λ,
        x 0 ∈ Λ.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin (n + 1) => E) 0) :=
      fun x hx => Submodule.mem_map.2 ⟨x, hx, rfl⟩
    obtain ⟨l1, hl1, hl1a⟩ := Submodule.mem_map.1 haI
    obtain ⟨l0, hl0, hl0a, hl0z⟩ : ∃ l0 ∈ Λ, l0 0 = a ∧ (a = 0 → l0 = 0) := by
      by_cases ha0 : a = 0
      · exact ⟨0, Λ.zero_mem, by simp [ha0], fun _ => rfl⟩
      · exact ⟨l1, hl1, hl1a, fun h => absurd h ha0⟩
    have hdec : ∀ v ∈ PI.LocLatEq.latL A Λ, ∃ c ∈ A.O, ∃ w ∈ PI.LocLatEq.latL A (Λ.comap L),
        v = c • PI.LocLatEq.bc A l0 + (Fin.cons (0 : A.Ep) w : Fin (n + 1) → A.Ep) := by
      intro v hv
      unfold PI.LocLatEq.latL at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, hl, rfl⟩ := hx
        obtain ⟨d, hd, r, hr⟩ := hgen (l 0) (hx0 l hl)
        obtain ⟨u, hu, hud⟩ := hU F E sig p A d hd
        obtain ⟨m, hm⟩ : ∃ m : Fin (n + 1) → E, m = algebraMap (𝓞 F) (𝓞 E) d • l - r • l0 :=
          ⟨_, rfl⟩
        have hm0 : m 0 = 0 := by
          rw [hm, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, hl0a, hr, sub_self]
        have hmc : (Fin.cons (0 : E) (Fin.tail m) : Fin (n + 1) → E) = m := by
          rw [← hm0, Fin.cons_self_tail]
        have hmt : Fin.tail m ∈ Λ.comap L := by
          rw [Submodule.mem_comap, hL, hmc, hm]
          exact Λ.sub_mem (Λ.smul_mem _ hl) (Λ.smul_mem _ hl0)
        have hr' : ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) * l 0 = (r : E) * a := by
          simpa only [ringOfIntegers_smul_eq_coe_mul] using hr
        refine ⟨u * A.ιE (r : E), A.O.mul_mem hu (core_int_mem A r),
          u • PI.LocLatEq.bc A (Fin.tail m),
          core_smem A (PI.LocLatEq.latL A (Λ.comap L)) hu
            (locLatEq_bc_mem_latL_of_mem A _ hmt), ?_⟩
        funext i
        cases i using Fin.cases with
        | zero =>
          simp only [locLatEq_bc_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero,
            add_zero, hl0a]
          have h1 := congrArg A.ιE hr'
          rw [map_mul, map_mul] at h1
          linear_combination (-(A.ιE (l 0))) * hud + u * h1
        | succ j =>
          simp only [locLatEq_bc_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_succ,
            Fin.tail, hm, Pi.sub_apply, ringOfIntegers_smul_eq_coe_mul, map_sub, map_mul]
          linear_combination (-(A.ιE (l j.succ))) * hud
      | zero =>
        refine ⟨0, A.O.zero_mem, 0, Submodule.zero_mem _, ?_⟩
        funext i
        cases i using Fin.cases <;> simp
      | add x y _ _ hx hy =>
        obtain ⟨c1, hc1, w1, hw1, rfl⟩ := hx
        obtain ⟨c2, hc2, w2, hw2, rfl⟩ := hy
        refine ⟨c1 + c2, A.O.add_mem hc1 hc2, w1 + w2, Submodule.add_mem _ hw1 hw2, ?_⟩
        funext i
        cases i using Fin.cases <;>
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, Fin.cons_succ,
            add_zero] <;> ring
      | smul o x _ hx =>
        obtain ⟨c, hc, w, hw, rfl⟩ := hx
        refine ⟨(o : A.Ep) * c, A.O.mul_mem o.2 hc, o • w, Submodule.smul_mem _ o hw, ?_⟩
        funext i
        cases i using Fin.cases <;>
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Subring.smul_def, Fin.cons_zero,
            Fin.cons_succ, add_zero] <;> ring
    have htail : ∀ v ∈ PI.LocLatEq.latL A Λ, v 0 = 0 →
        Fin.tail v ∈ PI.LocLatEq.latL A (Λ.comap L) := by
      intro v hv hv0
      obtain ⟨c, hc, w, hw, rfl⟩ := hdec v hv
      have hca : c * A.ιE a = 0 := by
        have h0 := hv0
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, add_zero,
          locLatEq_bc_apply, hl0a] at h0
        exact h0
      have hzero : c • PI.LocLatEq.bc A l0 = 0 := by
        by_cases ha0 : a = 0
        · rw [hl0z ha0]
          funext i
          simp [locLatEq_bc_apply]
        · have hc0 : c = c * A.ιE a * A.ιE a⁻¹ := by
            rw [mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, mul_one]
          rw [hca, zero_mul] at hc0
          rw [hc0, zero_smul]
      rw [hzero, zero_add, Fin.tail_cons]
      exact hw
    obtain ⟨c, hc, w, hw, hyd⟩ := hdec _ hy
    have hy0 : A.ιE (y 0) = c * A.ιE a := by
      have h0 := congrFun hyd 0
      simp only [locLatEq_bc_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero,
        add_zero, hl0a] at h0
      exact h0
    obtain ⟨t, ht, hta⟩ : ∃ t : E, A.ιE t ∈ A.O ∧ y 0 = t * a := by
      by_cases ha0 : a = 0
      · refine ⟨0, by rw [map_zero]; exact A.O.zero_mem, ?_⟩
        rw [ha0, map_zero, mul_zero] at hy0
        rw [zero_mul]
        exact A.ιE.injective (by rw [hy0, map_zero])
      · refine ⟨y 0 * a⁻¹, ?_, by rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]⟩
        rw [map_mul, hy0, mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, mul_one]
        exact hc
    obtain ⟨d1, hd1, b, hb⟩ := hI F E h2 sig p A t ht
    obtain ⟨z, hz⟩ : ∃ z : Fin (n + 1) → E, z = algebraMap (𝓞 F) (𝓞 E) d1 • y - b • l0 :=
      ⟨_, rfl⟩
    have hz0 : z 0 = 0 := by
      rw [hz, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, ringOfIntegers_smul_eq_coe_mul, ringOfIntegers_smul_eq_coe_mul,
        hl0a, hta]
      linear_combination a * hb
    have hzL : PI.LocLatEq.bc A z ∈ PI.LocLatEq.latL A Λ := by
      rw [hz, core_bc_sub, bc_smul, bc_smul]
      exact Submodule.sub_mem _
        (core_smem A (PI.LocLatEq.latL A Λ) (core_int_mem A _) hy)
        (core_smem A (PI.LocLatEq.latL A Λ) (core_int_mem A b)
          (locLatEq_bc_mem_latL_of_mem A Λ hl0))
    have ht' : PI.LocLatEq.bc A (Fin.tail z) ∈ PI.LocLatEq.latL A (Λ.comap L) :=
      htail _ hzL (by rw [locLatEq_bc_apply, hz0, map_zero])
    obtain ⟨d2, hd2, hd2z⟩ := ih (Λ.comap L) hFG (Fin.tail z) ht'
    have hzc : (Fin.cons (0 : E) (Fin.tail z) : Fin (n + 1) → E) = z := by
      rw [← hz0, Fin.cons_self_tail]
    have hz2 : algebraMap (𝓞 F) (𝓞 E) d2 • z ∈ Λ := by
      have h := Submodule.mem_comap.1 hd2z
      rwa [map_smul, hL, hzc] at h
    have hy' : algebraMap (𝓞 F) (𝓞 E) d1 • y = z + b • l0 := by
      rw [hz, sub_add_cancel]
    refine ⟨d2 * d1, mul_not_mem_asIdeal_of_not_mem hd2 hd1, ?_⟩
    rw [map_mul, mul_smul, hy', smul_add, smul_smul]
    exact Λ.add_mem hz2 (Λ.smul_mem _ hl0)
end PI.LocLatEq.W
