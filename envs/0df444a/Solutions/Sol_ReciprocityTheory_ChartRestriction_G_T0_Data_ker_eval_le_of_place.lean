-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.ker_eval_le_of_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:43:19.122037+00:00
-- url     : https://prove2.me/submissions/227eb297-240a-4751-8893-7fe2bf3dc959

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_psiS_chiImg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_psiS_chiImg_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sImg_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sH_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_w0rat_eq_base

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) {p : Ideal (KTp K d.D d.N)}
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) (hy : 0 < w (d.rationalBaseRow c)) :
    kerP (K := K) (D := d.D) (d.jc c) (d.x c) ≤ p := by
  obtain ⟨_, hw2⟩ := hw
  intro F hF
  have hF0 : chiP (K := K) (D := d.D) (d.jc c) (d.x c) F = 0 := RingHom.mem_ker.mp hF
  have hsH : ∀ v, 0 ≤ w (sImg (Ω := Ω c) (d.jc c) (d.x c) v) := fun v => by
    rw [← d.sH_X c v]
    exact (hw2 (MvPolynomial.X v)).1
  have hv : ∀ v : TVar d.D d.N, 0 ≤ w (psiS (chiImg (d.jc c) (d.x c) v)) ∧ 0 < w (sImg (Ω := Ω c) (d.jc c) (d.x c) v - psiS (chiImg (d.jc c) (d.x c) v)) := by
    intro v
    by_cases hv0 : v.1 = 0 ∧ v.2 = d.jc c
    · obtain ⟨v1, v2⟩ := v
      obtain ⟨h1, h2⟩ := hv0
      have h1' : v1 = 0 := h1
      have h2' : v2 = d.jc c := h2
      subst h1'
      subst h2'
      have hdiff : sImg (Ω := Ω c) (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c) - psiS (chiImg (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c)) =
          d.rationalBaseRow c := by
        rw [sImg_base, psiS_chiImg_base, d.w0rat_eq_base hd c, ← map_sub]
        congr 1
        ring
      rw [hdiff]
      refine ⟨?_, hy⟩
      have e : psiS (chiImg (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c)) =
          sImg (Ω := Ω c) (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c) - d.rationalBaseRow c := by
        rw [← hdiff]
        ring
      rw [e]
      exact le_trans (le_min (hsH _) hy.le) (AddValuation.map_sub _ _ _)
    · rw [psiS_chiImg (d.jc c) (d.x c) v hv0, sub_self, AddValuation.map_zero]
      exact ⟨hsH v, by simp⟩
  have hC : ∀ k : K, d.sH c (MvPolynomial.C k) = psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) (MvPolynomial.C k)) := by
    intro k
    have e1 : chiP (K := K) (D := d.D) (d.jc c) (d.x c) (MvPolynomial.C k) =
        algebraMap K (MvPolynomial (Fin (d.D + 1) × Fin d.N) (Ω c)) k := MvPolynomial.aeval_C _ _
    have e2 : d.sH c (MvPolynomial.C k) = algebraMap K (OmS (Ω c) d.D d.N) k :=
      MvPolynomial.aeval_C _ _
    rw [e1, e2]
    unfold psiS
    rw [RingHom.comp_apply]
    first
    | (rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
       exact IsScalarTower.algebraMap_apply K _ _ k)
    | (simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
       exact IsScalarTower.algebraMap_apply K _ _ k)
    | (simp [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)])
  have key : ∀ G : KTp K d.D d.N, 0 ≤ w (psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) G)) ∧ 0 < w (d.sH c G - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) G)) := by
    intro G
    induction G using MvPolynomial.induction_on
    · rename_i k
      rw [← hC k, sub_self, AddValuation.map_zero]
      exact ⟨(hw2 _).1, by simp⟩
    · rename_i p q hp hq
      simp only [map_add]
      refine ⟨le_trans (le_min hp.1 hq.1) (AddValuation.map_add _ _ _), ?_⟩
      have e : d.sH c p + d.sH c q - (psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p) + psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) q)) =
          (d.sH c p - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p)) + (d.sH c q - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) q)) := by ring
      rw [e]
      exact lt_of_lt_of_le (lt_min hp.2 hq.2) (AddValuation.map_add _ _ _)
    · rename_i p v hp
      have hX : chiP (K := K) (D := d.D) (d.jc c) (d.x c) (MvPolynomial.X v) = chiImg (d.jc c) (d.x c) v := MvPolynomial.aeval_X _ _
      rw [map_mul (chiP (K := K) (D := d.D) (d.jc c) (d.x c)) p (MvPolynomial.X v), hX,
        map_mul (psiS (Ω := Ω c) (D := d.D) (N := d.N)), map_mul (d.sH c) p (MvPolynomial.X v),
        d.sH_X c v]
      refine ⟨by rw [AddValuation.map_mul]; exact add_nonneg hp.1 (hv v).1, ?_⟩
      have e : d.sH c p * sImg (Ω := Ω c) (d.jc c) (d.x c) v - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p) * psiS (chiImg (d.jc c) (d.x c) v) =
          d.sH c p * (sImg (Ω := Ω c) (d.jc c) (d.x c) v - psiS (chiImg (d.jc c) (d.x c) v)) + (d.sH c p - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p)) * psiS (chiImg (d.jc c) (d.x c) v) := by ring
      rw [e]
      refine lt_of_lt_of_le (lt_min ?_ ?_) (AddValuation.map_add _ _ _)
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le (hv v).2 (le_add_of_nonneg_left (hw2 p).1)
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le hp.2 (le_add_of_nonneg_right (hv v).1)
  apply (hw2 F).2.mp
  have h := (key F).2
  rw [hF0, map_zero, sub_zero] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.T0.Data
