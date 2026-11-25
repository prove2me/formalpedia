-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.fix_all_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:27:03.377818+00:00
-- url     : https://prove2.me/submissions/746825f1-a839-4e22-a154-100a08892718

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SubProjOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SUEqClosure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_of_closure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_preserves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_gp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_stage4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_stage5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x) {i2 : K} (h2i : 2 * i2 = 1) {δ : K} (hδ : IsUnit δ)
  (hσδ : σ δ = -δ) [IsReduced K]
  (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
include hσ hJ he hff hef hfix h2i hδ hσδ
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {r : ℕ} (F : OFam σ J e f r) (hF : F.Spans) {h : Matrix ι ι K}
    (hpres : ∀ x y, hf σ J (h *ᵥ x) (h *ᵥ y) = hf σ J x y) (hfixa : ∀ j, h *ᵥ F.a j = F.a j) :
    h ∈ Good σ J e f := by
  have hae := F.ha_e
  have haf := F.ha_f
  have hlin : ∀ (k l : K) (x y z : ι → K),
      hf σ J (k • x + l • y) z = k * hf σ J x z + l * hf σ J y z := by
    intro k l x y z
    simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hsym : ∀ x y, hf σ J y x = σ (hf σ J x y) := fun x y => (hf_symm hσ hJ x y).symm
  have hfe : hf σ J f e = 1 := by rw [hsym, hef, map_one]
  have hea : ∀ j, hf σ J e (F.a j) = 0 := fun j => by rw [hsym, F.ha_e j, map_zero]
  have hfa : ∀ j, hf σ J f (F.a j) = 0 := fun j => by rw [hsym, F.ha_f j, map_zero]
  have hspan : ∀ x, (∀ j, hf σ J x (F.a j) = 0) → x = hf σ J x f • e + hf σ J x e • f := by
    intro x hx
    have h1 := hF x
    simp only [OFam.proj, hx, zero_mul, zero_smul, Finset.sum_const_zero, add_zero] at h1
    exact h1.symm
  have horth : ∀ (M : Matrix ι ι K), (∀ x y, hf σ J (M *ᵥ x) (M *ᵥ y) = hf σ J x y) →
      (∀ j, M *ᵥ F.a j = F.a j) → ∀ x, (∀ j, hf σ J x (F.a j) = 0) →
        ∀ j, hf σ J (M *ᵥ x) (F.a j) = 0 := by
    intro M hM hMa x hx j
    rw [← hMa j, hM, hx]

  set b := h *ᵥ e with hbdef
  set c := h *ᵥ f with hcdef
  clear_value b c
  have hba : ∀ j, hf σ J b (F.a j) = 0 := by rw [hbdef]; exact horth h hpres hfixa e hea
  have hca : ∀ j, hf σ J c (F.a j) = 0 := by rw [hcdef]; exact horth h hpres hfixa f hfa
  have hbform := hspan b hba
  have hcform := hspan c hca
  have hcb : hf σ J c b = 1 := by rw [hcdef, hbdef, hpres, hfe]
  have hcop : IsCoprime (hf σ J b f) (hf σ J b e) := by
    refine ⟨σ (hf σ J c e), σ (hf σ J c f), ?_⟩
    have h1 : hf σ J c f * σ (hf σ J b e) + hf σ J c e * σ (hf σ J b f) = 1 := by
      rw [← hcb]
      conv_rhs => rw [hcform]
      rw [hlin, hsym b e, hsym b f]
    have h2 := congrArg σ h1
    rw [map_add, map_mul, map_mul, hσ, hσ, map_one] at h2
    linear_combination h2
  obtain ⟨b4, r4, f4, u4⟩ : ∃ b', Reach σ J e f F.a b b' ∧ b' = hf σ J b' f • e + hf σ J b' e • f ∧
      IsUnit (hf σ J b' f) := by
    apply stage4 (hform := hbform) (hcop := hcop) <;> first | exact hδ | exact hσδ | assumption
  have i4 : (∀ j, hf σ J b4 (F.a j) = 0) ∧ hf σ J b4 b4 = hf σ J b b := by
    apply reach_inv (h := r4) (hb := hba) <;> first | exact hδ | exact hσδ | assumption
  have r5 : Reach σ J e f F.a b4 (e + (hf σ J b4 b4 * i2) • f) := by
    apply stage5 (hform := f4) (hα := u4) <;> first | exact hδ | exact hσδ | assumption
  have hbb : hf σ J b b = 0 := by rw [hbdef, hpres, he]
  rw [i4.2, hbb, zero_mul, zero_smul, add_zero] at r5
  have rt : Reach σ J e f F.a b e := by
    apply reach_trans (h1 := r4) (h2 := r5) <;> first | exact hδ | exact hσδ | assumption
  obtain ⟨p, hp, hpa, hpb⟩ := rt
  have gp : ∀ x y, hf σ J (p *ᵥ x) (p *ᵥ y) = hf σ J x y := by
    intro x y; exact good_preserves hσ hJ he hff hef hae haf hp x y
  set g := p * h with hgdef
  clear_value g
  have hgpres : ∀ x y, hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ J x y := by
    intro x y; rw [hgdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gp, hpres]
  have hga : ∀ j, g *ᵥ F.a j = F.a j := by
    intro j; rw [hgdef, ← Matrix.mulVec_mulVec, hfixa, hpa]
  have hge : g *ᵥ e = e := by rw [hgdef, ← Matrix.mulVec_mulVec, ← hbdef, hpb]
  set y := g *ᵥ f with hydef
  clear_value y
  have hya : ∀ j, hf σ J y (F.a j) = 0 := by rw [hydef]; exact horth g hgpres hga f hfa
  have hye : hf σ J y e = 1 := by rw [hydef, ← hge, hgpres, hfe]
  have hyy : hf σ J y y = 0 := by rw [hydef, hgpres, hff]
  set γ := hf σ J y f with hγ
  clear_value γ
  have hyform : y = γ • e + f := by
    have := hspan y hya
    rw [hye, one_smul, ← hγ] at this
    exact this
  have hγσ : γ + σ γ = 0 := by
    have h1 := hyy
    nth_rewrite 1 [hyform] at h1
    rw [show γ • e + f = γ • e + (1 : K) • f by rw [one_smul], hlin, hsym y e, hsym y f, hye,
      map_one, one_mul] at h1
    rw [hγ] at h1 ⊢
    linear_combination h1
  set E := eich σ J e 0 γ with hEdef
  clear_value E
  have hEm : E ∈ eichSet σ J e f :=
    Or.inl ⟨0, γ, by simp [hf], by simp [hf], by simp [hf, hγσ], hEdef⟩
  have hE : E ∈ Good σ J e f := by
    apply good_of_closure (hn := Submonoid.subset_closure hEm) <;> first | exact hδ | exact hσδ | assumption
  have h0 : ∀ x, hf σ J x 0 = 0 := fun x => by simp [hf]
  have key : ∀ x, g *ᵥ x = E *ᵥ x := by
    intro x
    have hx := hF x
    simp only [OFam.proj] at hx
    calc g *ᵥ x = g *ᵥ (hf σ J x f • e + hf σ J x e • f +
          ∑ j, (hf σ J x (F.a j) * F.inv j) • F.a j) := by rw [hx]
      _ = hf σ J x f • e + hf σ J x e • (γ • e + f) +
          ∑ j, (hf σ J x (F.a j) * F.inv j) • F.a j := by
        rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.mulVec_sum, hge, ← hydef, hyform]
        simp only [Matrix.mulVec_smul, hga]
      _ = (hf σ J x f • e + hf σ J x e • f + ∑ j, (hf σ J x (F.a j) * F.inv j) • F.a j) +
          (γ * hf σ J x e) • e := by
        rw [smul_add, smul_smul, mul_comm (hf σ J x e) γ]; abel
      _ = E *ᵥ x := by rw [hx, hEdef, eich_mulVec, h0]; simp
  have hgE : g = E := Matrix.toLin'.injective (LinearMap.ext fun x => by
    simp only [Matrix.toLin'_apply]; exact key x)
  obtain ⟨p', hp', hp'p, -⟩ : ∃ g' ∈ Good σ J e f, g' * p = 1 ∧ p * g' = 1 := by
    apply good_inv (hg := hp) <;> first | exact hδ | exact hσδ | assumption
  have : h = p' * g := by rw [hgdef, ← mul_assoc, hp'p, one_mul]
  rw [this, hgE]
  apply good_mul (hg := hp') (hg' := hE) <;> first | exact hδ | exact hσδ | assumption
end ReciprocityTheory.ChartRestriction.G.SA
