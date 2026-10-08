-- Prove2me | solution 1 for SionMinimax.KneserFan.theorem_4_1_prime
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:53:33.044784+00:00
-- url     : https://prove2.me/submissions/448a6b60-cb4d-4ffb-afce-dd96eef4f631

import Mathlib
import Definitions.Def_SionMinimax_KneserFan_Concavelike



namespace SionMinimax.KneserFan

open Classical in
lemma kf_L {M N : Type*} (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N) (Y : Finset N) (c : ℝ)
    (h : ∀ μ : M, ∃ y ∈ Y, f μ y < c) : ∃ ν : N, ∀ μ : M, f μ ν ≤ c := by
  obtain ⟨hcc, hcv⟩ := hf
  rcases isEmpty_or_nonempty M with hM | hM
  · rcases hne with h1 | h1
    · exact absurd h1 (not_nonempty_iff.mpr hM)
    · obtain ⟨ν⟩ := h1
      exact ⟨ν, fun μ => (IsEmpty.false μ).elim⟩
  obtain ⟨μ0⟩ := hM
  have hS : Convex ℝ {g : M → ℝ | ∃ ν : N, ∀ μ, f μ ν ≤ g μ} := by
    intro g1 hg1 g2 hg2 a b ha hb hab
    obtain ⟨ν1, h1⟩ := hg1
    obtain ⟨ν2, h2⟩ := hg2
    have hb' : b = 1 - a := by linarith
    subst hb'
    obtain ⟨ν, hν⟩ := hcv ν1 ν2 a ha (by linarith)
    refine ⟨ν, fun μ => ?_⟩
    have := hν μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e1 := mul_le_mul_of_nonneg_left (h1 μ) ha
    have e2 := mul_le_mul_of_nonneg_left (h2 μ) hb
    linarith
  have hCc : Convex ℝ {v : Y → ℝ | ∃ μ : M, ∀ y : Y, v y ≤ f μ y} := by
    intro v1 hv1 v2 hv2 a b ha hb hab
    obtain ⟨μ1, h1⟩ := hv1
    obtain ⟨μ2, h2⟩ := hv2
    have hb' : b = 1 - a := by linarith
    subst hb'
    obtain ⟨μ, hμ⟩ := hcc μ1 μ2 a ha (by linarith)
    refine ⟨μ, fun y => ?_⟩
    have := hμ y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e1 := mul_le_mul_of_nonneg_left (h1 y) ha
    have e2 := mul_le_mul_of_nonneg_left (h2 y) hb
    linarith
  have hKc : Convex ℝ (Set.pi Set.univ (fun _ : Y => Set.Ioi c)) :=
    convex_pi (fun _ _ => convex_Ioi c)
  have hKo : IsOpen (Set.pi Set.univ (fun _ : Y => Set.Ioi c)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioi)
  have hdisj : Disjoint (Set.pi Set.univ (fun _ : Y => Set.Ioi c))
      {v : Y → ℝ | ∃ μ : M, ∀ y : Y, v y ≤ f μ y} := by
    rw [Set.disjoint_left]
    intro v hvK hvC
    obtain ⟨μ, hμ⟩ := hvC
    obtain ⟨y, hy, hlt⟩ := h μ
    have h1 : c < v ⟨y, hy⟩ := hvK ⟨y, hy⟩ (Set.mem_univ _)
    have h2 : v ⟨y, hy⟩ ≤ f μ y := hμ ⟨y, hy⟩
    linarith
  obtain ⟨ℓ, u, hℓK, hℓC⟩ := geometric_hahn_banach_open hKc hKo hCc hdisj
  obtain ⟨a, hexp⟩ : ∃ a : Y → ℝ, ∀ v : Y → ℝ, ℓ v = ∑ y, v y * a y := by
    refine ⟨fun y => ℓ (fun j => if y = j then 1 else 0), fun v => ?_⟩
    have := LinearMap.pi_apply_eq_sum_univ (ℓ : (Y → ℝ) →ₗ[ℝ] ℝ) v
    simpa [smul_eq_mul] using this
  have hmemK : ∀ v : Y → ℝ, (∀ j, c < v j) → v ∈ Set.pi Set.univ (fun _ : Y => Set.Ioi c) :=
    fun v hv j _ => hv j
  have hsign : ∀ y : Y, a y ≤ 0 := by
    intro y
    by_contra hpos
    push_neg at hpos
    have hs : 0 < |u - ℓ (fun _ => c + 1)| / a y + 1 := by positivity
    have hmem := hmemK (fun j : Y => c + 1 + (if j = y then |u - ℓ (fun _ => c + 1)| / a y + 1 else 0))
      (fun j => by split_ifs <;> linarith)
    have h1 := hℓK _ hmem
    rw [hexp] at h1
    have h2 : ∑ j, (c + 1 + if j = y then |u - ℓ (fun _ => c + 1)| / a y + 1 else 0) * a j
        = ℓ (fun _ => c + 1) + (|u - ℓ (fun _ => c + 1)| / a y + 1) * a y := by
      rw [hexp (fun _ => c + 1)]
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [h2] at h1
    have h3 : (|u - ℓ (fun _ => c + 1)| / a y + 1) * a y = |u - ℓ (fun _ => c + 1)| + a y := by
      field_simp
    have h4 := le_abs_self (u - ℓ (fun _ => c + 1))
    linarith
  have hC' : ∀ μ : M, (fun y : Y => f μ y) ∈ {v : Y → ℝ | ∃ μ : M, ∀ y : Y, v y ≤ f μ y} :=
    fun μ => ⟨μ, fun y => le_rfl⟩
  have hmain : ∀ μ : M, ∀ e : ℝ, 0 < e →
      (c + e) * ∑ y : Y, a y < ∑ y : Y, f μ y * a y := by
    intro μ e he
    have h1 := hℓK (fun _ => c + e) (hmemK _ (fun j => by linarith))
    have h2 := hℓC _ (hC' μ)
    rw [hexp] at h1 h2
    rw [← Finset.mul_sum] at h1
    linarith
  have hA : ∑ y, a y < 0 := by
    by_contra hA
    push_neg at hA
    have hle : ∑ y, a y ≤ 0 := Finset.sum_nonpos (fun y _ => hsign y)
    have hz : ∀ y ∈ (Finset.univ : Finset Y), a y = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun y _ => hsign y)).mp (le_antisymm hle hA)
    have := hmain μ0 1 one_pos
    have e1 : ∑ y, a y = 0 := le_antisymm hle hA
    have e2 : ∑ y : Y, f μ0 y * a y = 0 := Finset.sum_eq_zero (fun y hy => by rw [hz y hy, mul_zero])
    rw [e1, e2] at this
    simp at this
  set A := ∑ y, a y with hAdef
  have hp0 : ∀ y ∈ (Finset.univ : Finset Y), 0 ≤ a y / A :=
    fun y _ => div_nonneg_of_nonpos (hsign y) hA.le
  have hp1 : ∑ y, a y / A = 1 := by
    rw [← Finset.sum_div]; exact div_self hA.ne
  have hmem := hS.sum_mem hp0 hp1 (z := fun (y : Y) (μ : M) => f μ y)
    (fun y _ => ⟨y, fun μ => le_rfl⟩)
  obtain ⟨ν, hν⟩ := hmem
  refine ⟨ν, fun μ => ?_⟩
  have h1 := hν μ
  rw [Finset.sum_apply] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  have h2 : ∑ y : Y, a y / A * f μ y ≤ c := by
    apply le_of_forall_pos_lt_add
    intro e he
    have := hmain μ e he
    have e3 : ∑ y : Y, a y / A * f μ y = (∑ y : Y, f μ y * a y) / A := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun y _ => by ring)
    rw [e3, div_lt_iff_of_neg hA]
    linarith
  linarith

lemma kf_Ld {M N : Type*} (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N) (X : Finset M) (c : ℝ)
    (h : ∀ ν : N, ∃ x ∈ X, c < f x ν) : ∃ μ : M, ∀ ν : N, c ≤ f μ ν := by
  have hg : ConcaveConvexlike (fun (ν : N) (μ : M) => -f μ ν) := by
    obtain ⟨hcc, hcv⟩ := hf
    refine ⟨?_, ?_⟩
    · intro ν1 ν2 t ht0 ht1
      obtain ⟨ν, hν⟩ := hcv ν1 ν2 t ht0 ht1
      exact ⟨ν, fun μ => by have := hν μ; linarith⟩
    · intro μ1 μ2 t ht0 ht1
      obtain ⟨μ, hμ⟩ := hcc μ1 μ2 t ht0 ht1
      exact ⟨μ, fun ν => by have := hμ ν; linarith⟩
  obtain ⟨μ, hμ⟩ := kf_L (fun (ν : N) (μ : M) => -f μ ν) hg hne.symm X (-c)
    (fun ν => by obtain ⟨x, hx, hlt⟩ := h ν; exact ⟨x, hx, by show -f x ν < -c; linarith⟩)
  exact ⟨μ, fun ν => by have : -f μ ν ≤ -c := hμ ν; linarith⟩

lemma kf_weak {M N : Type*} (f : M → N → ℝ) : supInf f ≤ infSup f := by
  unfold supInf infSup
  exact iSup_iInf_le_iInf_iSup _

lemma kf_le_of_exists {M N : Type*} (f : M → N → ℝ) (c : ℝ)
    (h : ∃ ν : N, ∀ μ : M, f μ ν ≤ c) : infSup f ≤ (c : EReal) := by
  obtain ⟨ν, hν⟩ := h
  calc infSup f ≤ ⨆ μ, ((f μ ν : ℝ) : EReal) := iInf_le _ ν
    _ ≤ c := iSup_le fun μ => by exact_mod_cast hν μ

lemma kf_ge_of_exists {M N : Type*} (f : M → N → ℝ) (c : ℝ)
    (h : ∃ μ : M, ∀ ν : N, c ≤ f μ ν) : (c : EReal) ≤ supInf f := by
  obtain ⟨μ, hμ⟩ := h
  calc (c : EReal) ≤ ⨅ ν, ((f μ ν : ℝ) : EReal) := le_iInf fun ν => by exact_mod_cast hμ ν
    _ ≤ supInf f := le_iSup (fun μ => ⨅ ν, ((f μ ν : ℝ) : EReal)) μ

theorem kf41p_core {M N : Type*} (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (hfin : ∀ c : ℝ, supInf f < (c : EReal) →
      ∃ Y : Finset N, ∀ μ : M, ∃ y ∈ Y, f μ y < c) :
    supInf f = infSup f := by
  refine le_antisymm (kf_weak f) ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨Y, hY⟩ := hfin c h1
  exact absurd h2 (not_lt.mpr (kf_le_of_exists f c (kf_L f hf hne Y c hY)))

theorem kf41_core {M N : Type*} (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (hfin : ∀ c : ℝ, (c : EReal) < infSup f →
      ∃ X : Finset M, ∀ ν : N, ∃ x ∈ X, c < f x ν) :
    supInf f = infSup f := by
  refine le_antisymm (kf_weak f) ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨X, hX⟩ := hfin c h2
  exact absurd h1 (not_lt.mpr (kf_ge_of_exists f c (kf_Ld f hf hne X c hX)))

theorem kf42p_core {M N : Type*} [TopologicalSpace N] [CompactSpace N]
    (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (hlsc : ∀ μ : M, LowerSemicontinuous (fun ν : N => f μ ν)) :
    supInf f = infSup f := by
  refine le_antisymm (kf_weak f) ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hfip : (Set.univ ∩ ⋂ μ : M, {ν : N | f μ ν ≤ c}).Nonempty := by
    apply IsCompact.inter_iInter_nonempty isCompact_univ
    · intro μ; exact (hlsc μ).isClosed_preimage c
    · intro u
      have : ∃ ν : N, ∀ μ ∈ u, f μ ν ≤ c := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨μ, hμ⟩ := kf_Ld f hf hne u c hcon
        exact absurd h1 (not_lt.mpr (kf_ge_of_exists f c ⟨μ, hμ⟩))
      obtain ⟨ν, hν⟩ := this
      refine ⟨ν, trivial, ?_⟩
      simp only [Set.mem_iInter₂]
      exact hν
  obtain ⟨ν, -, hν⟩ := hfip
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hν
  exact absurd h2 (not_lt.mpr (kf_le_of_exists f c ⟨ν, hν⟩))

theorem kf42_core {M N : Type*} [TopologicalSpace M] [CompactSpace M]
    (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (husc : ∀ ν : N, UpperSemicontinuous (fun μ : M => f μ ν)) :
    supInf f = infSup f := by
  refine le_antisymm (kf_weak f) ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hfip : (Set.univ ∩ ⋂ ν : N, {μ : M | c ≤ f μ ν}).Nonempty := by
    apply IsCompact.inter_iInter_nonempty isCompact_univ
    · intro ν; exact (husc ν).isClosed_preimage c
    · intro u
      have : ∃ μ : M, ∀ ν ∈ u, c ≤ f μ ν := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨ν, hν⟩ := kf_L f hf hne u c hcon
        exact absurd h2 (not_lt.mpr (kf_le_of_exists f c ⟨ν, hν⟩))
      obtain ⟨μ, hμ⟩ := this
      refine ⟨μ, trivial, ?_⟩
      simp only [Set.mem_iInter₂]
      exact hμ
  obtain ⟨μ, -, hμ⟩ := hfip
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hμ
  exact absurd h1 (not_lt.mpr (kf_ge_of_exists f c ⟨μ, hμ⟩))

end SionMinimax.KneserFan

open SionMinimax.KneserFan


theorem solution {M N : Type*} (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (hfin : ∀ c : ℝ, supInf f < (c : EReal) →
      ∃ Y : Finset N, ∀ μ : M, ∃ y ∈ Y, f μ y < c) :
    supInf f = infSup f := by
  exact kf41p_core f hf hne hfin
