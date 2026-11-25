-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.exists_ext_cochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:34.008215+00:00
-- url     : https://prove2.me/submissions/1fe57606-cb29-4157-95d7-05004d6cbc02

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_exists_cont_select
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_cj_coe
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_isOpen_setOf_conj_eq
import Theorems.Thm_ReciprocityTheory_Coh_groupSection_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.InflationTransgression.cj_coe

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.InflationTransgression
theorem _root_.solution [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal] (hNc : IsClosed (N : Set G))
    (f : N → M.V) (hf : Continuous f) (hfc : ∀ a b : N, f (a * b) = f a + M.rho a (f b))
    (hinv : ∀ s : G, ∃ m : M.V, ∀ n : N, M.rho s (f (cj N s n)) - f n = M.rho n m - m) :
    ∃ y : G → M.V, Continuous y ∧ (∀ n : N, y n = f n) ∧
      (∀ g (n : N), y (g * n) = y g + M.rho g (f n)) ∧
      (∀ (n : N) g, y (n * g) = f n + M.rho n (y g)) := by
  have : Nonempty M.V := ⟨0⟩
  obtain ⟨ψ, hψc, hψ⟩ := exists_cont_select
    (fun s m => ∀ n : N, M.rho s (f (cj N s n)) - f n = M.rho n m - m)
    (isOpen_setOf_conj_eq M N hNc f hf) hinv
  obtain ⟨r, hrc, hr1, hr⟩ := groupSection_holds G N hNc
  have hf1 : f 1 = 0 := by
    have e := hfc 1 1
    simp only [mul_one, OneMemClass.coe_one, map_one, Module.End.one_apply] at e
    exact (left_eq_add.1 e)
  have hψ1 : ∀ n : N, M.rho n (ψ 1) = ψ 1 := fun n => by
    have e := hψ 1 n
    have hc : cj N 1 n = n := Subtype.ext (by simp)
    rw [hc, map_one, Module.End.one_apply, sub_self] at e
    exact (sub_eq_zero.1 e.symm)
  have hrσ : ∀ g, r ((r g : G)⁻¹ * g) = 1 := fun g => by
    have e := hr (r g)⁻¹ g
    rw [InvMemClass.coe_inv] at e
    rw [e, inv_mul_cancel]
  set σ : G → G := fun g => (r g : G)⁻¹ * g with hσ
  set y : G → M.V := fun g => f (r g) + M.rho (r g) (ψ (σ g)) - ψ 1 with hy
  have hσn : ∀ (n : N) g, σ (n * g) = σ g := fun n g => by
    simp only [hσ, hr n g, Subgroup.coe_mul, mul_inv_rev]; group
  have h3 : ∀ (n : N) g, y (n * g) = f n + M.rho n (y g) := fun n g => by
    simp only [hy, hσn, hr n g, hfc, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add,
      map_sub, hψ1]
    abel
  have h2 : ∀ g (n : N), y (g * n) = y g + M.rho g (f n) := fun g n => by
    set t := σ g with ht
    let n'' : N := ⟨t * n * t⁻¹, (inferInstance : N.Normal).conj_mem n n.2 t⟩
    have hg : (r g : G) * t = g := by simp [ht, hσ]
    have e1 : g * n = ((r g * n'' : N) : G) * t := by
      simp only [Subgroup.coe_mul, n'']
      calc g * n = (r g : G) * t * n := by rw [hg]
        _ = _ := by group
    have hrgn : r (g * n) = r g * n'' := by rw [e1, hr, hrσ g, mul_one]
    have hσgn : σ (g * n) = t := by
      show ((r (g * n) : G))⁻¹ * (g * n) = t
      rw [hrgn, e1]; group
    have hc : cj N t n'' = n := Subtype.ext (by simp [n'']; group)
    have e2 := hψ t n''
    rw [hc] at e2
    have e3 : f n'' + M.rho n'' (ψ t) = M.rho t (f n) + ψ t := by
      rw [sub_eq_sub_iff_add_eq_add] at e2
      rw [add_comm (f n''), ← e2]
    have hrg : M.rho g = M.rho (r g) * M.rho t := by rw [← map_mul, hg]
    show f (r (g * n)) + M.rho (r (g * n)) (ψ (σ (g * n))) - ψ 1 = y g + M.rho g (f n)
    rw [hrgn, hσgn, hfc]
    calc _ = f (r g) + M.rho (r g) (f n'' + M.rho n'' (ψ t)) - ψ 1 := by
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add]; abel
      _ = f (r g) + M.rho (r g) (M.rho t (f n) + ψ t) - ψ 1 := by rw [e3]
      _ = _ := by rw [map_add, hrg, Module.End.mul_apply, hy]; simp only [← ht]; abel
  have hy1 : y 1 = 0 := by simp [hy, hr1, hf1, hσ]
  refine ⟨y, ?_, fun n => by simpa [hy1] using h3 n 1, h2, h3⟩
  have hr' : Continuous fun g => (r g : G) := continuous_subtype_val.comp hrc
  exact ((hf.comp hrc).add (M.cont.comp (hr'.prodMk (hψc.comp (hr'.inv.mul continuous_id))))).sub
    continuous_const
end ReciprocityTheory.Coh.InflationTransgression
