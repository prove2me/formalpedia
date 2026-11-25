-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AlgRes.exists_goodChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:44:36.446327+00:00
-- url     : https://prove2.me/submissions/9ee3d1b7-5570-4551-bd1d-edbc16f5d3b5

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AtlasA
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_holo_coords
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
namespace ReciprocityTheory.AnForm.R
namespace AlgRes
theorem _root_.solution (R : AlgRes ι P D e) (i : Fin R.n) (x : R.M) (hx : x ∈ R.src i)
    (r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ)
    (hr : Ideal.span (Set.range fun l => algebraMap _ (locRing (R.ideal i) (R.coord i x)) (r l)) =
      Ideal.map (algebraMap _ (locRing (R.ideal i) (R.coord i x))) (ptIdeal (R.coord i x)))
    (O : Set R.M) (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ), R.GoodChart ψ ∧ x ∈ ψ.source ∧
      ψ.source ⊆ O ∩ R.src i ∧ ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y) := by
  have := R.regular i x hx
  obtain ⟨U, V, g, hU, hpU, hV, hg, hbij, hrg⟩ :=
    exists_holo_coords (R.ideal i) (R.coord i x) e (R.dim i x hx) r hr
  have hcont : ContinuousOn (R.coord i) (R.src i) := by
    rw [continuousOn_iff_continuous_domRestrict]; exact (R.isEmbedding i).continuous
  have hinj : Set.InjOn (R.coord i) (R.src i) := fun a ha b hb hab =>
    congrArg Subtype.val ((R.isEmbedding i).injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  have hev : Continuous (evalFam r) := continuous_pi fun l => MvPolynomial.continuous_eval (p := r l)
  have hzero : ∀ y ∈ R.src i, R.coord i y ∈ zeroSet (R.ideal i) := by
    intro y hy
    have : R.coord i y ∈ R.coord i '' R.src i := ⟨y, hy, rfl⟩
    rw [R.image i] at this
    exact this
  have hex : ∀ w ∈ V, ∃ y ∈ R.src i, R.coord i y = g w := by
    intro w hw
    have h1 : g w ∈ zeroSet (R.ideal i) := (hbij.mapsTo hw).2
    have hmem : g w ∈ R.coord i '' R.src i := by rw [R.image i]; exact h1
    obtain ⟨y, hy, hyw⟩ := hmem
    exact ⟨y, hy, hyw⟩
  classical
  let inv : (Fin e → ℂ) → R.M := fun w =>
    if h : ∃ y ∈ R.src i, R.coord i y = g w then h.choose else x
  have hinv : ∀ w ∈ V, inv w ∈ R.src i ∧ R.coord i (inv w) = g w := by
    intro w hw
    have h := hex w hw
    simp only [inv, dif_pos h]
    exact h.choose_spec
  have hback : ∀ y ∈ R.src i, R.coord i y ∈ U → g (evalFam r (R.coord i y)) = R.coord i y := by
    intro y hy hyU
    obtain ⟨w, hw, hgw⟩ := hbij.surjOn ⟨hyU, hzero y hy⟩
    rw [← hgw, hrg w hw]
  let S : Set R.M := R.src i ∩ R.coord i ⁻¹' (U ∩ evalFam r ⁻¹' V)
  have hSo : IsOpen S := hcont.isOpen_inter_preimage (R.isOpen_alt_bis i) (hU.inter (hV.preimage hev))
  have hmapT : ∀ w ∈ V, inv w ∈ S := by
    intro w hw
    obtain ⟨h1, h2⟩ := hinv w hw
    refine ⟨h1, ?_⟩
    show R.coord i (inv w) ∈ U ∩ evalFam r ⁻¹' V
    rw [h2]
    refine ⟨(hbij.mapsTo hw).1, ?_⟩
    show evalFam r (g w) ∈ V
    rw [hrg w hw]
    exact hw
  have hcinv : ContinuousOn inv V := by
    rw [continuousOn_iff_continuous_domRestrict]
    let f : V → R.src i := fun w => ⟨inv w, (hinv w w.2).1⟩
    have hf : Continuous f := by
      rw [(R.isEmbedding i).continuous_iff]
      have : ((fun y : R.src i => R.coord i y) ∘ f) = fun w : V => g w :=
        funext fun w => (hinv w w.2).2
      rw [this]
      exact hg.continuousOn.domRestrict
    exact continuous_subtype_val.comp hf
  let ψ0 : OpenPartialHomeomorph R.M (Fin e → ℂ) :=
    { toFun := fun y => evalFam r (R.coord i y)
      invFun := inv
      source := S
      target := V
      map_source' := fun y hy => hy.2.2
      map_target' := fun w hw => hmapT w hw
      left_inv' := fun y hy => by
        obtain ⟨h1, h2⟩ := hinv _ hy.2.2
        exact hinj h1 hy.1 (h2.trans (hback y hy.1 hy.2.1))
      right_inv' := fun w hw => by
        obtain ⟨-, h2⟩ := hinv w hw
        show evalFam r (R.coord i (inv w)) = w
        rw [h2, hrg w hw]
      open_source := hSo
      open_target := hV
      continuousOn_toFun := (hev.comp_continuousOn hcont).mono fun y hy => hy.1
      continuousOn_invFun := hcinv }
  have hxS : x ∈ S := by
    obtain ⟨w, hw, hgw⟩ := hbij.surjOn ⟨hpU, hzero x hx⟩
    refine ⟨hx, hpU, ?_⟩
    show evalFam r (R.coord i x) ∈ V
    rw [← hgw, hrg w hw]
    exact hw
  refine ⟨ψ0.restrOpen O hO, ⟨i, fun y hy => hy.1.1, ⟨r, fun y _ => rfl⟩, g,
    hg.mono fun w hw => hw.1, fun w hw => (hinv w hw.1).2⟩, ⟨hxS, hxO⟩,
    fun y hy => ⟨hy.2, hy.1.1⟩, fun y _ => rfl⟩
end AlgRes
end ReciprocityTheory.AnForm.R
