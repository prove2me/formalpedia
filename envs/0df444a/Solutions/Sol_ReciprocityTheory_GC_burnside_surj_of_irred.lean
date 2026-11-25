-- Prove2me | solution 1 for ReciprocityTheory.GC.burnside_surj_of_irred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:50.161798+00:00
-- url     : https://prove2.me/submissions/4b65ee22-a30b-4891-afae-3ee4c7dc5d51

import Mathlib
import Definitions.Def_ReciprocityTheory_BurnsideSurjectivity_Burnside
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.GC
private lemma exists_mem_apply_eq_lemma {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (B : Subalgebra k (Module.End k V))
    (hB : ∀ W : Submodule k V, (∀ b ∈ B, ∀ w ∈ W, b w ∈ W) → W = ⊥ ∨ W = ⊤)
    {x : V} (hx : x ≠ 0) (y : V) : ∃ b ∈ B, b x = y := by
  obtain ⟨W, hWm⟩ : ∃ W : Submodule k V, ∀ v, v ∈ W ↔ ∃ b ∈ B, b x = v :=
    ⟨{ carrier := {v | ∃ b ∈ B, b x = v}
       add_mem' := by
         rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
         exact ⟨b + c, B.add_mem hb hc, rfl⟩
       zero_mem' := ⟨0, B.zero_mem, rfl⟩
       smul_mem' := by
         rintro r _ ⟨b, hb, rfl⟩
         exact ⟨r • b, B.smul_mem hb r, rfl⟩ }, fun v => Iff.rfl⟩
  have hW : ∀ b ∈ B, ∀ w ∈ W, b w ∈ W := by
    intro b hb w hw
    obtain ⟨c, hc, rfl⟩ := (hWm w).1 hw
    exact (hWm _).2 ⟨b * c, B.mul_mem hb hc, rfl⟩
  rcases hB W hW with h | h
  · exfalso
    have hxW : x ∈ W := (hWm x).2 ⟨1, B.one_mem, rfl⟩
    rw [h] at hxW
    exact hx ((Submodule.mem_bot k).1 hxW)
  · have hyW : y ∈ W := by rw [h]; exact Submodule.mem_top
    exact (hWm y).1 hyW
private lemma mem_of_irred_lemma_2 {k V : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (B : Subalgebra k (Module.End k V))
    (hB : ∀ W : Submodule k V, (∀ b ∈ B, ∀ w ∈ W, b w ∈ W) → W = ⊥ ∨ W = ⊤)
    (f : Module.End k V) : f ∈ B := by
  classical
  have h10 : (1 : Module.End k V) ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (LinearMap.congr_fun h v)

  have hex : ∃ r, ∃ T ∈ B, T ≠ 0 ∧ Module.finrank k (LinearMap.range T) = r :=
    ⟨_, 1, B.one_mem, h10, rfl⟩
  obtain ⟨T, hTB, hT0, hTr⟩ := Nat.find_spec hex
  have hmin : ∀ T' ∈ B, T' ≠ 0 → Nat.find hex ≤ Module.finrank k (LinearMap.range T') :=
    fun T' h1 h2 => Nat.find_min' hex ⟨T', h1, h2, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, T u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hT0 (LinearMap.ext h)
  haveI : Nontrivial (LinearMap.range T) :=
    ⟨⟨⟨T u, LinearMap.mem_range_self T u⟩, 0, fun h => hu (congrArg Subtype.val h)⟩⟩

  have key : ∀ b ∈ B, ∃ c : k, T * b * T = c • T := by
    intro b hb
    have hRinv : ∀ v ∈ LinearMap.range T, (T * b) v ∈ LinearMap.range T :=
      fun v _ => LinearMap.mem_range_self T (b v)
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((T * b).restrict hRinv)
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hw0 : w ≠ 0 := hw.2
    have hTbw : T (b (w : V)) = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨c, ?_⟩
    by_contra hne
    have hT'B : T * b * T - c • T ∈ B :=
      B.sub_mem (B.mul_mem (B.mul_mem hTB hb) hTB) (B.smul_mem hTB c)
    have hle := hmin _ hT'B (sub_ne_zero.2 hne)
    have hcomp : T * b * T - c • T = (T * b - c • 1).comp T := by
      ext v; rfl
    rw [hcomp, LinearMap.range_comp, ← LinearMap.range_domRestrict] at hle
    have hsum := LinearMap.finrank_range_add_finrank_ker
      ((T * b - c • 1).domRestrict (LinearMap.range T))
    have hker : w ∈ LinearMap.ker ((T * b - c • 1).domRestrict (LinearMap.range T)) := by
      rw [LinearMap.mem_ker]
      show T (b (w : V)) - c • (w : V) = 0
      rw [hTbw, sub_self]
    have hk : Module.finrank k
        (LinearMap.ker ((T * b - c • 1).domRestrict (LinearMap.range T))) ≠ 0 := by
      intro h0
      rw [Submodule.finrank_eq_zero] at h0
      rw [h0] at hker
      exact hw0 ((Submodule.mem_bot k).1 hker)
    omega

  have hTv : ∀ v, ∃ c : k, T v = c • T u := by
    intro v
    obtain ⟨b, hb, hbv⟩ := exists_mem_apply_eq_lemma B hB hu v
    obtain ⟨c, hc⟩ := key b hb
    refine ⟨c, ?_⟩
    rw [← hbv]
    exact LinearMap.congr_fun hc u
  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual k V, χ (T u) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu ((Module.forall_dual_apply_eq_zero_iff k (T u)).1 h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k V, ∀ v, φ v = (χ (T u))⁻¹ * χ (T v) :=
    ⟨(χ (T u))⁻¹ • (χ ∘ₗ T), fun v => rfl⟩
  have hφT : ∀ v, T v = φ v • T u := by
    intro v
    obtain ⟨c, hc⟩ := hTv v
    rw [hφ v, hc, map_smul, smul_eq_mul, mul_comm c, ← mul_assoc, inv_mul_cancel₀ hχ, one_mul]
  have hφu : φ u = 1 := by
    rw [hφ u]
    exact inv_mul_cancel₀ hχ

  obtain ⟨S, hSm⟩ : ∃ S : Submodule k (Module.Dual k V),
      ∀ ψ, ψ ∈ S ↔ ∀ y : V, ψ.smulRight y ∈ B :=
    ⟨{ carrier := {ψ | ∀ y : V, ψ.smulRight y ∈ B}
       add_mem' := by
         intro ψ χ' hψ hχ' y
         have h : (ψ + χ').smulRight y = ψ.smulRight y + χ'.smulRight y := by
           ext v; simp [add_smul]
         rw [h]; exact B.add_mem (hψ y) (hχ' y)
       zero_mem' := by
         intro y
         have h : (0 : Module.Dual k V).smulRight y = 0 := by
           ext v; simp
         rw [h]; exact B.zero_mem
       smul_mem' := by
         intro r ψ hψ y
         have h : (r • ψ).smulRight y = r • ψ.smulRight y := by
           ext v; simp [mul_smul]
         rw [h]; exact B.smul_mem (hψ y) r }, fun ψ => Iff.rfl⟩
  have hφS : φ ∈ S := by
    rw [hSm]
    intro y
    obtain ⟨b, hb, hby⟩ := exists_mem_apply_eq_lemma B hB hu y
    have h : φ.smulRight y = b * T := by
      ext v
      show φ v • y = b (T v)
      rw [hφT v, map_smul, hby]
    rw [h]
    exact B.mul_mem hb hTB
  have hScomp : ∀ ψ ∈ S, ∀ b ∈ B, ψ ∘ₗ b ∈ S := by
    intro ψ hψ b hb
    rw [hSm] at hψ ⊢
    intro y
    have h : (ψ ∘ₗ b).smulRight y = ψ.smulRight y * b := by
      ext v; rfl
    rw [h]
    exact B.mul_mem (hψ y) hb

  have hU : S.dualCoannihilator = ⊥ := by
    have hinv : ∀ b ∈ B, ∀ w ∈ S.dualCoannihilator, b w ∈ S.dualCoannihilator := by
      intro b hb w hw
      rw [Submodule.mem_dualCoannihilator] at hw ⊢
      intro ψ hψ
      exact hw _ (hScomp ψ hψ b hb)
    rcases hB _ hinv with h | h
    · exact h
    · exfalso
      have hu' : u ∈ S.dualCoannihilator := by rw [h]; exact Submodule.mem_top
      rw [Submodule.mem_dualCoannihilator] at hu'
      have h1 := hu' φ hφS
      rw [hφu] at h1
      exact one_ne_zero h1
  have hStop : S = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := S), hU,
      Submodule.dualAnnihilator_bot]
  obtain ⟨bs⟩ : Nonempty (Module.Basis (Fin (Module.finrank k V)) k V) := ⟨Module.finBasis k V⟩
  have hf : f = ∑ i, (bs.coord i).smulRight (f (bs i)) := by
    refine bs.ext fun j => ?_
    simp [LinearMap.sum_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rw [hf]
  refine sum_mem fun i _ => ?_
  have hmem : bs.coord i ∈ S := by rw [hStop]; exact Submodule.mem_top
  rw [hSm] at hmem
  exact hmem _
end ReciprocityTheory.GC
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GC
namespace ReciprocityTheory.GC
theorem _root_.solution {k A V : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : A →ₐ[k] Module.End k V) [Nontrivial V]
    (hirr : ∀ W : Submodule k V, (∀ a : A, ∀ w ∈ W, ρ a w ∈ W) → W = ⊥ ∨ W = ⊤) : Function.Surjective ρ := by
  intro f
  have hB : ∀ W : Submodule k V, (∀ b ∈ ρ.range, ∀ w ∈ W, b w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hirr W fun a w hw => hW (ρ a) (AlgHom.mem_range_self ρ a) w hw
  exact (AlgHom.mem_range ρ).1 (mem_of_irred_lemma_2 ρ.range hB f)
end ReciprocityTheory.GC
