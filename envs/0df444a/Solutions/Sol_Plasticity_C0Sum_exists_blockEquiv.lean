-- Prove2me | solution 1 for Plasticity.C0Sum.exists_blockEquiv
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:57.07804+00:00
-- url     : https://prove2.me/submissions/b689f885-1c8d-44bb-908e-66e62020b693

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_support
import Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_no_fed

/-!
The block bijection for c₀ sums of scalar and non-parallelogram planar blocks (CUB103, CUB109
§§2–3): assembled from the forward-support part card and the no-fed-blocks part card.

The c₀-sum helpers `norm_c0Sum_le`, `norm_apply_le`, `c0_ext`, `ofFun`, `sg` are copied from the
project's solution `Solutions/Sol_Plasticity_C0Sum_exists_extremeRule.lean`.
-/

open Plasticity

namespace Sol_Plasticity_C0Sum_exists_blockEquiv

open Classical

section C0

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

lemma norm_c0Sum_le {x : c0Sum E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖(x : lp E ⊤) i‖ ≤ C) :
    ‖x‖ ≤ C := by
  rw [Submodule.coe_norm]
  exact lp.norm_le_of_forall_le hC h

lemma norm_apply_le (x : c0Sum E) (i : ι) : ‖(x : lp E ⊤) i‖ ≤ ‖x‖ := by
  rw [Submodule.coe_norm]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ i

/-- The function with blocks `f m` on a finite set `S` and zero elsewhere. -/
noncomputable def ofFunFun (S : Finset ι) (f : ∀ m, E m) : ∀ m, E m :=
  fun m => if m ∈ S then f m else 0

omit [∀ i, NormedSpace ℝ (E i)] in
lemma norm_ofFunFun_le (S : Finset ι) (f : ∀ m, E m) (m : ι) :
    ‖ofFunFun S f m‖ ≤ ∑ n ∈ S, ‖f n‖ := by
  unfold ofFunFun
  split_ifs with h
  · exact Finset.single_le_sum (f := fun n => ‖f n‖) (fun n _ => norm_nonneg _) h
  · rw [norm_zero]
    exact Finset.sum_nonneg fun n _ => norm_nonneg _

omit [∀ i, NormedSpace ℝ (E i)] in
lemma memℓp_ofFunFun (S : Finset ι) (f : ∀ m, E m) : Memℓp (ofFunFun S f) ⊤ := by
  refine memℓp_infty ⟨∑ n ∈ S, ‖f n‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  exact norm_ofFunFun_le S f m

lemma mem_c0Sum_ofFunFun (S : Finset ι) (f : ∀ m, E m) :
    (⟨ofFunFun S f, memℓp_ofFunFun S f⟩ : lp E ⊤) ∈ c0Sum E := by
  show Filter.Tendsto (fun m => ‖ofFunFun S f m‖) Filter.cofinite (nhds 0)
  refine tendsto_nhds_of_eventually_eq ?_
  refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
  intro m hm
  by_contra h
  have h' : m ∉ S := fun h'' => h (Finset.mem_coe.2 h'')
  exact hm (by simp [ofFunFun, h'])

/-- The point of `c0Sum E` with blocks `f m` on `S` and zero elsewhere. -/
noncomputable def ofFun (S : Finset ι) (f : ∀ m, E m) : c0Sum E :=
  ⟨⟨ofFunFun S f, memℓp_ofFunFun S f⟩, mem_c0Sum_ofFunFun S f⟩

lemma ofFun_apply (S : Finset ι) (f : ∀ m, E m) (m : ι) :
    ((ofFun S f : c0Sum E) : lp E ⊤) m = if m ∈ S then f m else 0 := rfl

/-- The point of `c0Sum E` with block `a` at `j` and zero elsewhere. -/
noncomputable def sg (j : ι) (a : E j) : c0Sum E := ofFun {j} (Function.update 0 j a)

lemma sg_self (j : ι) (a : E j) : ((sg j a : c0Sum E) : lp E ⊤) j = a := by
  simp [sg, ofFun_apply]

lemma sg_ne {j m : ι} (a : E j) (h : m ≠ j) : ((sg j a : c0Sum E) : lp E ⊤) m = 0 := by
  simp [sg, ofFun_apply, h]

lemma norm_sg_le (j : ι) (a : E j) : ‖sg j a‖ ≤ ‖a‖ := by
  refine norm_c0Sum_le (norm_nonneg _) fun m => ?_
  by_cases h : m = j
  · subst h; rw [sg_self]
  · rw [sg_ne a h, norm_zero]; exact norm_nonneg _

end C0

end Sol_Plasticity_C0Sum_exists_blockEquiv

open Sol_Plasticity_C0Sum_exists_blockEquiv in
theorem solution {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ (Module.finrank ℝ (E' k) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E' k) 1)).encard))
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1)) :
    ∃ σ : ι ≃ κ, (∀ i, Module.finrank ℝ (E' (σ i)) = Module.finrank ℝ (E i)) ∧
      ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ i,
        ‖(F x : lp E' ⊤) (σ i)‖ ≤ ‖(x : lp E ⊤) i‖ := by
  classical
  obtain ⟨σ, hsurj, hsupp, hplane, hscal, hthree⟩ :=
    Plasticity.C0Sum.exists_blockEquiv_support E E' hE (fun k => (hE' k).imp id And.left)
      F hbij hlip
  have hnofed := Plasticity.C0Sum.exists_blockEquiv_no_fed E E' hE hE' F hbij hlip σ hsupp
    (fun i hi => (hplane i hi).2) hscal hthree
  have hinj : Function.Injective σ := by
    intro a b hab
    rcases hE a with ha | ⟨ha, _⟩
    · rcases hE b with hb | ⟨hb, _⟩
      · exact (hscal a b (hnofed a ha) hab.symm).symm
      · exact (hplane b hb).2 a hab
    · exact ((hplane a ha).2 b hab.symm).symm
  have hbijσ : Function.Bijective σ := ⟨hinj, hsurj⟩
  refine ⟨Equiv.ofBijective σ hbijσ, fun i => ?_, fun x hx i => ?_⟩
  · show Module.finrank ℝ (E' (σ i)) = _
    rcases hE i with hi | ⟨hi, _⟩
    · rw [hnofed i hi, hi]
    · rw [(hplane i hi).1, hi]
  · show ‖(F x : lp E' ⊤) (σ i)‖ ≤ _
    set x' : c0Sum E := x - sg i ((x : lp E ⊤) i) with hx'
    have hx'i : ∀ k, (x' : lp E ⊤) k = if k = i then 0 else (x : lp E ⊤) k := by
      intro k
      split_ifs with h
      · subst h; simp [hx', sg_self]
      · simp [hx', sg_ne _ h]
    have hx'mem : x' ∈ Metric.closedBall (0 : c0Sum E) 1 := by
      rw [mem_closedBall_zero_iff]
      refine norm_c0Sum_le zero_le_one fun k => ?_
      rw [hx'i]
      split_ifs
      · simp
      · exact (norm_apply_le x k).trans (mem_closedBall_zero_iff.1 hx)
    have h0 : (F x' : lp E' ⊤) (σ i) = 0 := by
      refine hsupp x' hx'mem (σ i) fun k hk => ?_
      rw [hx'i, if_pos (hinj hk)]
    have hlipx := hlip.norm_sub_le hx hx'mem
    have hdiff : x - x' = sg i ((x : lp E ⊤) i) := by rw [hx']; abel
    calc ‖(F x : lp E' ⊤) (σ i)‖ = ‖((F x - F x' : c0Sum E') : lp E' ⊤) (σ i)‖ := by
          simp [h0]
      _ ≤ ‖F x - F x'‖ := norm_apply_le _ _
      _ ≤ ‖x - x'‖ := by simpa using hlipx
      _ ≤ ‖(x : lp E ⊤) i‖ := by rw [hdiff]; exact norm_sg_le _ _
