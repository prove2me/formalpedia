-- Prove2me | solution 1 for Representation.exists_const_apply_central_mul_eq_of_countable_translates_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2cf9ca46-798e-5db7-a023-93e0d2ea78c4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_const_apply_central_mul_eq_of_countable_translates_of_irreducible

set_option autoImplicit false

noncomputable section

open Polynomial Cardinal

universe u

namespace CountableSchur

variable {G : Type u} [Group G]

def R (h : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun w := fun g => w (g * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem R_apply (h : G) (w : G → ℂ) (g : G) : R h w g = w (g * h) := rfl

theorem R_coe (h : G) (w : G → ℂ) : (R h w : G → ℂ) = fun g => w (g * h) := rfl

theorem R_mul (h h' : G) (w : G → ℂ) : R h (R h' w) = R (h * h') w := by
  funext g
  simp only [R_apply, mul_assoc]

theorem R_one (w : G → ℂ) : R (1 : G) w = w := by
  funext g
  simp only [R_apply, mul_one]

def cyc (w : G → ℂ) : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range fun h : G => R h w)

theorem range_R_eq (w : G → ℂ) :
    (Set.range fun h : G => R h w) = Set.range fun h : G => fun g : G => w (g * h) := rfl

theorem cyc_eq (w : G → ℂ) :
    cyc w = Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)) := rfl

theorem R_mem_cyc (h : G) (w : G → ℂ) : R h w ∈ cyc w := Submodule.subset_span ⟨h, rfl⟩

theorem self_mem_cyc (w : G → ℂ) : w ∈ cyc w := by
  have := R_mem_cyc 1 w
  rwa [R_one] at this

theorem R_mem_cyc_of_mem {w u : G → ℂ} (h : G) (hu : u ∈ cyc w) : R h u ∈ cyc w := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h', rfl⟩ := hx
    rw [R_mul]
    exact R_mem_cyc _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem cyc_le_of_mem {w u : G → ℂ} (hu : u ∈ cyc w) : cyc u ≤ cyc w :=
  Submodule.span_le.mpr (by
    rintro _ ⟨h, rfl⟩
    exact R_mem_cyc_of_mem h hu)

section Central

variable (z : G) (hz : ∀ g : G, z * g = g * z)
include hz

theorem R_comm (h : G) (w : G → ℂ) : R z (R h w) = R h (R z w) := by
  rw [R_mul, R_mul, hz]

theorem pow_R_comm (h : G) (n : ℕ) (w : G → ℂ) : (R z ^ n) (R h w) = R h ((R z ^ n) w) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [R_comm z hz, ih]

theorem aeval_R_comm (P : ℂ[X]) (h : G) (w : G → ℂ) :
    aeval (R z) P (R h w) = R h (aeval (R z) P w) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, pow_R_comm z hz, map_smul]

end Central

theorem pow_R_mem_cyc (z : G) {w u : G → ℂ} (n : ℕ) (hu : u ∈ cyc w) : (R z ^ n) u ∈ cyc w := by
  induction n with
  | zero => simpa using hu
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact R_mem_cyc_of_mem z ih

theorem aeval_mem_cyc (z : G) (P : ℂ[X]) {w u : G → ℂ} (hu : u ∈ cyc w) : aeval (R z) P u ∈ cyc w := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun n _ => ?_
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (pow_R_mem_cyc z n hu)

theorem aeval_X_sub_C_apply (z : G) (a : ℂ) (w : G → ℂ) :
    aeval (R z) (X - C a) w = R z w - a • w := by
  rw [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]

section Main

variable {f : G → ℂ} (hf : f ≠ 0)
  (hirr : ∀ w ∈ cyc f, w ≠ 0 → f ∈ cyc w)
  (z : G) (hz : ∀ g : G, z * g = g * z)

include hz in

theorem R_eq_smul_of_eigen (hirr : ∀ w ∈ cyc f, w ≠ 0 → f ∈ cyc w)
    {a : ℂ} {w : G → ℂ} (hw : w ∈ cyc f) (hw0 : w ≠ 0)
    (heig : R z w = a • w) : R z f = a • f := by
  have hfw : f ∈ cyc w := hirr w hw hw0

  have key : ∀ x ∈ cyc w, R z x = a • x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [R_comm z hz, heig, map_smul]
    | zero => rw [map_zero, smul_zero]
    | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
    | smul c x _ hx => rw [map_smul, hx, smul_comm]
  exact key f hfw

include hf hirr hz in

theorem exists_preimage (hinj : ∀ a : ℂ, ∀ w ∈ cyc f, R z w - a • w = 0 → w = 0) (a : ℂ) :
    ∃ v ∈ cyc f, R z v - a • v = f := by
  set u : G → ℂ := R z f - a • f with hu_def
  have hu : u ∈ cyc f :=
    Submodule.sub_mem _ (R_mem_cyc_of_mem z (self_mem_cyc f)) (Submodule.smul_mem _ _ (self_mem_cyc f))
  have hu0 : u ≠ 0 := fun h0 => hf (hinj a f (self_mem_cyc f) h0)
  have hfu : f ∈ cyc u := hirr u hu hu0

  have key : ∀ x ∈ cyc u, ∃ v ∈ cyc f, R z v - a • v = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      refine ⟨R h f, R_mem_cyc h f, ?_⟩
      rw [R_comm z hz, ← map_smul, ← map_sub]
    | zero => exact ⟨0, Submodule.zero_mem _, by rw [map_zero, smul_zero, sub_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨v₁, hv₁, rfl⟩ := hx
      obtain ⟨v₂, hv₂, rfl⟩ := hy
      exact ⟨v₁ + v₂, Submodule.add_mem _ hv₁ hv₂, by rw [map_add, smul_add]; abel⟩
    | smul c x _ hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact ⟨c • v, Submodule.smul_mem _ _ hv, by rw [map_smul, smul_sub, smul_comm]⟩
  exact key f hfu

theorem aeval_eq_zero_imp (hinj : ∀ a : ℂ, ∀ w ∈ cyc f, R z w - a • w = 0 → w = 0) :
    ∀ (n : ℕ) (P : ℂ[X]), P.natDegree = n → P ≠ 0 →
      ∀ w ∈ cyc f, aeval (R z) P w = 0 → w = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hPn hP w hw h0
    by_cases hdeg : P.natDegree = 0
    · obtain ⟨c, hc⟩ : ∃ c, P = C c := ⟨_, Polynomial.eq_C_of_natDegree_eq_zero hdeg⟩
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hP (by rw [hc, map_zero])
      rw [hc, aeval_C, Module.algebraMap_end_apply] at h0
      exact (smul_eq_zero.mp h0).resolve_left hc0
    · have hd : 0 < P.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
      obtain ⟨r, hr⟩ := Complex.exists_root hd
      obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hr
      have hQ0 : Q ≠ 0 := by
        rintro rfl
        exact hP (by rw [hQ, mul_zero])
      have hQdeg : Q.natDegree < n := by
        have hmul := Polynomial.natDegree_mul (X_sub_C_ne_zero r) hQ0
        rw [← hQ, natDegree_X_sub_C, hPn] at hmul
        omega
      have hQw : aeval (R z) Q w ∈ cyc f := aeval_mem_cyc z Q hw
      have h1 : R z (aeval (R z) Q w) - r • aeval (R z) Q w = 0 := by
        rw [hQ, map_mul, Module.End.mul_apply, aeval_X_sub_C_apply] at h0
        exact h0
      have h2 : aeval (R z) Q w = 0 := hinj r _ hQw h1
      exact ih _ hQdeg Q rfl hQ0 w hw h2

include hf hirr hz in

theorem exists_eigen (hcount : (Set.range fun h : G => R h f).Countable) :
    ∃ (a : ℂ) (w : G → ℂ), w ∈ cyc f ∧ w ≠ 0 ∧ R z w = a • w := by
  by_contra hne
  push Not at hne
  have hinj : ∀ a : ℂ, ∀ w ∈ cyc f, R z w - a • w = 0 → w = 0 := by
    intro a w hw h0
    by_contra hw0
    exact hne a w hw hw0 (sub_eq_zero.mp h0)

  choose v hv using exists_preimage hf hirr z hz hinj

  have hli : LinearIndependent ℂ v := by
    classical
    rw [linearIndependent_iff']
    intro s c hsum a₀ ha₀

    set P : ℂ[X] := ∑ a ∈ s, C (c a) * ∏ b ∈ s.erase a, (X - C b) with hP_def
    set Pfull : ℂ[X] := ∏ b ∈ s, (X - C b) with hPfull_def

    have hPf : aeval (R z) P f = 0 := by
      have hterm : ∀ a ∈ s, aeval (R z) (C (c a) * ∏ b ∈ s.erase a, (X - C b)) f =
          aeval (R z) Pfull (c a • v a) := by
        intro a ha
        conv_lhs => rw [← (hv a).2]
        rw [← aeval_X_sub_C_apply, ← Module.End.mul_apply, ← map_mul, mul_assoc,
          Finset.prod_erase_mul _ _ ha, map_mul, aeval_C, Module.End.mul_apply,
          Module.algebraMap_end_apply, ← map_smul]
      rw [hP_def, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl hterm, ← map_sum, hsum, map_zero]

    have hP0 : P = 0 := by
      by_contra hP0
      exact hf (aeval_eq_zero_imp z hinj P.natDegree P rfl hP0 f (self_mem_cyc f) hPf)

    have heval : P.eval a₀ = c a₀ * ∏ b ∈ s.erase a₀, (a₀ - b) := by
      rw [hP_def, eval_finsetSum, Finset.sum_eq_single a₀]
      · rw [eval_mul, eval_C, eval_prod]
        simp only [eval_sub, eval_X, eval_C]
      · intro a ha hne'
        rw [eval_mul, eval_prod]
        have hmem : a₀ ∈ s.erase a := Finset.mem_erase.mpr ⟨fun h => hne' h.symm, ha₀⟩
        rw [Finset.prod_eq_zero hmem (by simp), mul_zero]
      · intro h
        exact absurd ha₀ h
    have hprod : ∏ b ∈ s.erase a₀, (a₀ - b) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun b hb => sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm
    have : c a₀ * ∏ b ∈ s.erase a₀, (a₀ - b) = 0 := by rw [← heval, hP0, eval_zero]
    exact (mul_eq_zero.mp this).resolve_right hprod

  have hli' : LinearIndependent ℂ (fun a : ℂ => (⟨v a, (hv a).1⟩ : cyc f)) :=
    LinearIndependent.of_comp (cyc f).subtype hli
  have h1 := hli'.cardinal_lift_le_rank
  have h2 : Module.rank ℂ (cyc f) ≤ #(Set.range fun h : G => R h f) := rank_span_le _
  have h3 : #(Set.range fun h : G => R h f) ≤ ℵ₀ := by
    haveI := hcount.to_subtype
    exact Cardinal.mk_le_aleph0_iff.mpr inferInstance
  have h4 : Cardinal.lift.{u} #ℂ ≤ ℵ₀ :=
    h1.trans ((Cardinal.lift_le.mpr (h2.trans h3)).trans_eq Cardinal.lift_aleph0)
  rw [Cardinal.mk_complex, Cardinal.lift_continuum] at h4
  exact absurd h4 (not_le.mpr Cardinal.aleph0_lt_continuum)

end Main

end CountableSchur

end

theorem solution
    {G : Type*} [Group G] (f : G → ℂ)
    (hcount : (Set.range fun h : G => fun g : G => f (g * h)).Countable)
    (hf : f ≠ 0)
    (hirr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => f (g * h)),
      w ≠ 0 → f ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)))
    (z : G) (hz : ∀ g : G, z * g = g * z) :
    ∃ c : ℂ, ∀ g : G, f (z * g) = c * f g := by
  have hirr' : ∀ w ∈ CountableSchur.cyc f, w ≠ 0 → f ∈ CountableSchur.cyc w := hirr
  have hcount' : (Set.range fun h : G => CountableSchur.R h f).Countable := hcount
  obtain ⟨a, w, hw, hw0, heig⟩ := CountableSchur.exists_eigen hf hirr' z hz hcount'
  have hRf : CountableSchur.R z f = a • f := CountableSchur.R_eq_smul_of_eigen z hz hirr' hw hw0 heig
  refine ⟨a, fun g => ?_⟩
  have key := congrFun hRf g
  rw [CountableSchur.R_apply, Pi.smul_apply, smul_eq_mul] at key
  rw [hz g]
  exact key

end S_Representation_exists_const_apply_central_mul_eq_of_countable_translates_of_irreducible
end P2MW
export P2MW.S_Representation_exists_const_apply_central_mul_eq_of_countable_translates_of_irreducible (solution)
