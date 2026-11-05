-- Prove2me | solution 1 for StrongConv.vanishesNear_supp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:56:15.754329+00:00
-- url     : https://prove2.me/submissions/124ba647-149f-4878-a9d4-7424041b65cc

import Definitions.Def_StrongConv
import Mathlib

section
section
open Polynomial Filter Topology Manifold

namespace StrongConv.Stable.VanSupp

open StrongConv

/-- An open set on which `f` vanishes, containing `A`. -/
lemma exists_open_of_eventually {A : Set ℝ} {f : ℝ → ℝ} (hf : ∀ᶠ x in 𝓝ˢ A, f x = 0) :
    ∃ W : Set ℝ, IsOpen W ∧ A ⊆ W ∧ ∀ x ∈ W, f x = 0 := by
  obtain ⟨W, hW, hAW, hWs⟩ := mem_nhdsSet_iff_exists.mp hf
  exact ⟨W, hW, hAW, fun x hx => hWs hx⟩

lemma eventually_of_open {W A : Set ℝ} {f : ℝ → ℝ} (hW : IsOpen W) (hAW : A ⊆ W)
    (hf : ∀ x ∈ W, f x = 0) : ∀ᶠ x in 𝓝ˢ A, f x = 0 :=
  Filter.Eventually.filter_mono (nhdsSet_mono hAW)
    (Filter.mem_of_superset (hW.mem_nhdsSet.mpr subset_rfl) hf)

lemma vanishesNear_univ (ν : smoothFun →ₗ[ℝ] ℝ) : VanishesNear ν Set.univ := by
  intro f hf
  obtain ⟨W, -, hW, hf0⟩ := exists_open_of_eventually hf
  have : f = 0 := Subtype.ext (funext fun x => hf0 x (hW (Set.mem_univ x)))
  rw [this, map_zero]

lemma vanishesNear_inter (ν : smoothFun →ₗ[ℝ] ℝ) {A B : Set ℝ} (hA : IsClosed A)
    (hB : IsClosed B) (hνA : VanishesNear ν A) (hνB : VanishesNear ν B) :
    VanishesNear ν (A ∩ B) := by
  intro f hf
  obtain ⟨W, hWo, hABW, hfW⟩ := exists_open_of_eventually hf
  have hs : IsClosed (B \ W) := hB.sdiff hWo
  have ht : IsClosed (A \ W) := hA.sdiff hWo
  have hd : Disjoint (B \ W) (A \ W) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxB, hxW⟩ ⟨hxA, -⟩
    exact hxW (hABW ⟨hxA, hxB⟩)
  obtain ⟨χ, hχ0, hχ1, -⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, ℝ) (n := (⊤ : ℕ∞)) hs ht hd
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ : ℝ → ℝ) := χ.contMDiff.contDiff
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f : ℝ → ℝ) := f.2
  let g₁ : smoothFun := ⟨fun x => χ x * (f : ℝ → ℝ) x, hχs.mul hfs⟩
  let g₂ : smoothFun := ⟨fun x => (1 - χ x) * (f : ℝ → ℝ) x, (contDiff_const.sub hχs).mul hfs⟩
  have hsum : f = g₁ + g₂ := by
    apply Subtype.ext
    funext x
    show (f : ℝ → ℝ) x = χ x * (f : ℝ → ℝ) x + (1 - χ x) * (f : ℝ → ℝ) x
    ring
  have hfWev : ∀ᶠ x in 𝓝ˢ W, (f : ℝ → ℝ) x = 0 := eventually_of_open hWo subset_rfl hfW
  have h₁ : ν g₁ = 0 := by
    apply hνB
    have hBsub : B ⊆ (B \ W) ∪ W := fun x hx => by
      by_cases hxW : x ∈ W
      · exact Or.inr hxW
      · exact Or.inl ⟨hx, hxW⟩
    refine Filter.Eventually.filter_mono (nhdsSet_mono hBsub) ?_
    rw [nhdsSet_union, eventually_sup]
    refine ⟨hχ0.mono fun x hx => ?_, hfWev.mono fun x hx => ?_⟩
    · show χ x * (f : ℝ → ℝ) x = 0
      rw [hx, zero_mul]
    · show χ x * (f : ℝ → ℝ) x = 0
      rw [hx, mul_zero]
  have h₂ : ν g₂ = 0 := by
    apply hνA
    have hAsub : A ⊆ (A \ W) ∪ W := fun x hx => by
      by_cases hxW : x ∈ W
      · exact Or.inr hxW
      · exact Or.inl ⟨hx, hxW⟩
    refine Filter.Eventually.filter_mono (nhdsSet_mono hAsub) ?_
    rw [nhdsSet_union, eventually_sup]
    refine ⟨hχ1.mono fun x hx => ?_, hfWev.mono fun x hx => ?_⟩
    · show (1 - χ x) * (f : ℝ → ℝ) x = 0
      rw [hx, sub_self, zero_mul]
    · show (1 - χ x) * (f : ℝ → ℝ) x = 0
      rw [hx, mul_zero]
  rw [hsum, map_add, h₁, h₂, add_zero]

lemma vanishesNear_Icc (ν : smoothFun →ₗ[ℝ] ℝ) {c K : ℝ} {m : ℕ} (hc : 0 < c)
    (hb : ∀ f : smoothFun, |ν f| ≤ c * cNorm m f (-K) K) :
    VanishesNear ν (Set.Icc (-K) K) := by
  intro f hf
  rw [eventually_nhdsSet_iff_forall] at hf
  have hle : cNorm m f (-K) K ≤ 0 := by
    unfold cNorm
    apply Finset.sum_nonpos
    intro j _
    unfold supOn
    apply Real.sSup_nonpos
    rintro _ ⟨x, hx, rfl⟩
    have h0 : (f : ℝ → ℝ) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := hf x hx
    show |iteratedDeriv j (f : ℝ → ℝ) x| ≤ 0
    rw [h0.iteratedDeriv_eq]
    simp
  have : |ν f| ≤ 0 := (hb f).trans (mul_nonpos_of_nonneg_of_nonpos hc.le hle)
  exact abs_nonpos_iff.mp this

theorem vanishesNear_supp_dev (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) :
    VanishesNear ν (supp ν) := by
  obtain ⟨c, K, m, hc, -, hb⟩ := hν
  set F : Set (Set ℝ) := {A | IsClosed A ∧ VanishesNear ν A} with hF
  intro f hf
  obtain ⟨U, hUo, hsU, hfU⟩ := exists_open_of_eventually hf
  have hcpt : IsCompact (Set.Icc (-K) K ∩ Uᶜ) := isCompact_Icc.inter_right hUo.isClosed_compl
  have hempty : (Set.Icc (-K) K ∩ Uᶜ) ∩ ⋂ i : F, (i : Set ℝ) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iInter, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro ⟨_, hxU⟩ hx
    apply hxU
    apply hsU
    rw [supp, Set.mem_sInter]
    intro A hA
    exact hx ⟨A, hA⟩
  obtain ⟨u, hu⟩ := hcpt.elim_finite_subfamily_closed (fun i : F => (i : Set ℝ))
    (fun i => i.2.1) hempty
  have hP : ∀ u : Finset F, IsClosed (⋂ i ∈ u, (i : Set ℝ)) ∧
      VanishesNear ν (⋂ i ∈ u, (i : Set ℝ)) := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ]
      exact ⟨isClosed_univ, vanishesNear_univ ν⟩
    | insert a s _ ih =>
      rw [Finset.set_biInter_insert]
      exact ⟨a.2.1.inter ih.1, vanishesNear_inter ν a.2.1 ih.1 a.2.2 ih.2⟩
  obtain ⟨hPc, hPv⟩ := hP u
  have hA : VanishesNear ν (Set.Icc (-K) K ∩ ⋂ i ∈ u, (i : Set ℝ)) :=
    vanishesNear_inter ν isClosed_Icc hPc (vanishesNear_Icc ν hc hb) hPv
  apply hA
  refine eventually_of_open hUo ?_ hfU
  rintro x ⟨hxI, hxu⟩
  by_contra hxU
  have : x ∈ (Set.Icc (-K) K ∩ Uᶜ) ∩ ⋂ i ∈ u, (i : Set ℝ) := ⟨⟨hxI, hxU⟩, hxu⟩
  rw [hu] at this
  exact this

end StrongConv.Stable.VanSupp

end
end

section
open StrongConv

open Polynomial Filter Topology


theorem solution (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) :
    VanishesNear ν (supp ν) := by
  apply StrongConv.Stable.VanSupp.vanishesNear_supp_dev <;> assumption

end
