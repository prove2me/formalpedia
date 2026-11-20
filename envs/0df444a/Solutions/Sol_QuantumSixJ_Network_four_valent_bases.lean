-- Prove2me | solution 1 for QuantumSixJ.Network.four_valent_bases
-- status  : ACCEPTED   (prove)
-- author  : @igor.kh
-- created : 2026-11-13T11:18:01.628355+00:00
-- url     : https://prove2.me/submissions/48f0e020-674f-4e5e-9dce-730ce89fb8f2

import Definitions.Def_QuantumSixJNetwork
import Theorems.Thm_QuantumSixJ_scalar_foundations

open CategoryTheory MonoidalCategory
universe v u
noncomputable section
open QuantumSixJ
open scoped BigOperators QuantumSixJ Classical

private def q_ne_zero := QuantumSixJ.scalar_foundations.1
private def q_denominator_ne_zero := QuantumSixJ.scalar_foundations.2.1
private def qInt_ne_zero := QuantumSixJ.scalar_foundations.2.2.1
private def qFactorial_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.1
private def delta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.1
private def theta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.1
private def h_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.1
private def x_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.1
private def tet_summand_support_bounds := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.1
private def tet_appendix_bounds_within_coarse := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.2.1

open CategoryTheory MonoidalCategory
open QuantumSixJ


namespace QuantumSixJ.Network

/-- For a three-leg covector whose third rotation is itself, the two nested
left/right mates of its first rotation agree. -/
lemma pivot2_rotate_mates_of_rotate3 {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (a b l : ℕ)
    (f : S.V l ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C)
    (h3 : Vertex.rotate (Vertex.rotate (Vertex.rotate f)) = f) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    (tensorLeftHomEquiv (S.V l) (S.V a) (S.V a) (S.V b))
      ((tensorLeftHomEquiv
        (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C))
        (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom) =
    (tensorRightHomEquiv (S.V l) (S.V b) (S.V b) (S.V a))
      ((tensorRightHomEquiv
        (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C))
        ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
          (λ_ (S.V a)).hom) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let eLb := tensorLeftHomEquiv
    (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C)
  let eLa := tensorLeftHomEquiv
    (S.V l) (S.V a) (S.V a) (S.V b)
  let eRa := tensorRightHomEquiv
    (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)
  let eRb := tensorRightHomEquiv
    (S.V l) (S.V b) (S.V b) (S.V a)
  let close (h : S.V l ⟶ S.V a ⊗ S.V b) :
      S.V l ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C :=
    (α_ (S.V l) (S.V b) (S.V a)).inv ≫
      eRa.symm (eRb.symm h ≫ (λ_ (S.V a)).inv)
  have close_injective : Function.Injective close := by
    intro x y hxy
    apply eRb.symm.injective
    rw [← cancel_mono (λ_ (S.V a)).inv]
    apply eRa.symm.injective
    rw [← cancel_epi (α_ (S.V l) (S.V b) (S.V a)).inv]
    exact hxy
  have close_right :
      close (eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
        (λ_ (S.V a)).hom)) = f := by
    simp only [close, Equiv.symm_apply_apply, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have close_left_rotate3 :
      close (eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom)) =
        Vertex.rotate (Vertex.rotate (Vertex.rotate f)) := by
    simp [close, eLa, eLb, eRa, eRb,
      tensorLeftHomEquiv, tensorRightHomEquiv,
      Vertex.rotate, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation, monoidalComp]
    monoidal
  change
    eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom) =
      eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
        (λ_ (S.V a)).hom)
  apply close_injective
  calc
    close (eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom)) =
        Vertex.rotate (Vertex.rotate (Vertex.rotate f)) := close_left_rotate3
    _ = f := h3
    _ = close (eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
      (λ_ (S.V a)).hom)) := close_right.symm

/-- Cyclicity supplies the third-rotation identity for every chosen vertex. -/
lemma pivot2_cup_split {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S)
    (hW : VertexNormalized W) (a b l : ℕ) :
    S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv
    (𝟙_ C) (S.V l) (S.V l) (S.V a ⊗ S.V b)
  let eLa := tensorLeftHomEquiv
    (S.V l) (S.V a) (S.V a) (S.V b)
  let eLb := tensorLeftHomEquiv
    (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C)
  let eRa := tensorRightHomEquiv
    (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)
  let eRb := tensorRightHomEquiv
    (S.V l) (S.V b) (S.V b) (S.V a)
  let r : S.V l ⟶ S.V a ⊗ S.V b :=
    eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ W.vertex l b a) ≫
      (λ_ (S.V a)).hom)
  have hsplit : W.split l a b =
      eLa (eLb (W.vertex b a l) ≫ (ρ_ (S.V b)).hom) := by
    dsimp [eLa, eLb, tensorLeftHomEquiv]
    simp only [Vertex.split, SuQ2Data.cup, ExactPairing.coevaluation]
    monoidal
  have hup : W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv =
      e ((λ_ (S.V l)).hom ≫ r) := by
    dsimp [e, r, eRa, eRb, tensorRightHomEquiv]
    simp only [Vertex.vertexUp, SuQ2Data.cup, ExactPairing.coevaluation]
    monoidal
  have hrot3 :
      Vertex.rotate (Vertex.rotate (Vertex.rotate (W.vertex l b a))) =
        W.vertex l b a := by
    rw [hW.cyclic l b a, hW.cyclic b a l, hW.cyclic a l b]
  have hm : W.split l a b = r := by
    rw [hsplit, ← hW.cyclic l b a]
    exact pivot2_rotate_mates_of_rotate3 S a b l (W.vertex l b a) hrot3
  calc
    S.cup l ≫ (W.split l a b ▷ S.V l) =
        e ((λ_ (S.V l)).hom ≫ W.split l a b) := by
      simp [e, tensorRightHomEquiv, SuQ2Data.cup,
        ExactPairing.coevaluation, comp_whiskerRight, unitors_equal]
    _ = e ((λ_ (S.V l)).hom ≫ r) := by rw [hm]
    _ = W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv := hup.symm

private lemma iota_delta_ne_zero_aux (l : ℕ) : ι (Δ (l : ℤ)) ≠ 0 := by
  apply (map_ne_zero_iff _ _).2 (delta_ne_zero l (by omega))
  unfold ι
  apply RatFunc.map_injective
  · exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective)
  · exact Polynomial.map_injective _ (algebraMap ℚ ℂ).injective

private lemma fuse_cap_aux {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ) :
    (W.fuse a b l ▷ S.V l) ≫ S.cap l =
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let f := (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l
  have hfuse : W.fuse a b l =
      (tensorRightHomEquiv (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C)) f ≫
        (λ_ (S.V l)).hom := by
    simp [f, Vertex.fuse, tensorRightHomEquiv, monoidalComp,
      SuQ2Data.cup, SuQ2Data.cap, ExactPairing.coevaluation,
      ExactPairing.evaluation]
  rw [hfuse]
  simpa [f, tensorRightHomEquiv, monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
    ExactPairing.coevaluation, ExactPairing.evaluation, ← unitors_equal] using
    (tensorRightHomEquiv (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C)).left_inv f

private lemma closed_assembly_aux {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ)
    (hcup : S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv)
    (hfuse : (W.fuse a b l ▷ S.V l) ≫ S.cap l =
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l) :
    S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
      W.vertexUp a b l ≫ W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc (S.cup l) (W.split l a b ▷ S.V l), hcup]
  simp only [Category.assoc]
  rw [hfuse]
  simp

private lemma unit_scalar_injective_aux {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) :
    Function.Injective (fun r : K => r • 𝟙 (𝟙_ C)) := by
  intro r s hrs
  have hrs0 : r • 𝟙 (S.V 0) = s • 𝟙 (S.V 0) := by
    have h := congrArg (fun f : 𝟙_ C ⟶ 𝟙_ C => S.unitIso.hom ≫ f ≫ S.unitIso.inv) hrs
    simpa [smul_smul] using h
  have hd : (0 : S.V 0 ⟶ S.V 0) = (r - s) • 𝟙 (S.V 0) := by
    rw [sub_smul, hrs0, sub_self]
  have hz : (0 : S.V 0 ⟶ S.V 0) = (0 : K) • 𝟙 (S.V 0) := by simp
  exact sub_eq_zero.mp ((hS.simple 0 0).unique hd hz)

private lemma bubble_from_closed_aux {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (a b l : ℕ) (u : K)
    (hclosed : S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
      u • 𝟙 (𝟙_ C)) :
    W.split l a b ≫ W.fuse a b l = (u / ι (Δ (l : ℤ))) • 𝟙 (S.V l) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have hunit := unit_scalar_injective_aux S hS
  obtain ⟨s, hs, _⟩ := hS.simple l (W.split l a b ≫ W.fuse a b l)
  have hclosed' : S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
      (s * ι (Δ (l : ℤ))) • 𝟙 (𝟙_ C) := by
    rw [hs]
    simp [hS.loop, smul_smul]
  have hscalar : s * ι (Δ (l : ℤ)) = u := by
    apply hunit
    exact hclosed'.symm.trans hclosed
  have hΔ := iota_delta_ne_zero_aux l
  have hsval : s = u / ι (Δ (l : ℤ)) := (eq_div_iff hΔ).2 hscalar
  rw [← hsval]
  exact hs

private lemma split_fuse_normalized_aux {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W)
    (a b l : ℕ) :
    W.split l a b ≫ W.fuse a b l =
      (ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ))) • 𝟙 (S.V l) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  apply bubble_from_closed_aux S W hS a b l (ι (θ (a : ℤ) b l))
  calc
    S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
        W.vertexUp a b l ≫ W.vertex a b l :=
      closed_assembly_aux S W a b l (pivot2_cup_split S W hW a b l)
        (fuse_cap_aux S W a b l)
    _ = ι (θ (a : ℤ) b l) • 𝟙 (𝟙_ C) := hW.theta a b l

private lemma admissible_swap_aux (a b c : ℤ) :
    Admissible a b c ↔ Admissible a c b := by
  constructor <;>
    rintro ⟨ha, hb, hc, h₁, h₂, h₃, h₄⟩ <;>
    refine ⟨ha, hc, hb, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma theta_swap_aux (a b c : ℤ) : θ a b c = θ a c b := by
  have hs : Admissible a b c ↔ Admissible a c b := admissible_swap_aux a b c
  by_cases h₁ : Admissible a b c
  · have h₂ : Admissible a c b := hs.mp h₁
    simp only [θ, if_pos h₁, if_pos h₂]
    rw [show a + b + c = a + c + b by ring]
    ring
  · have h₂ : ¬ Admissible a c b := fun h => h₁ (hs.mpr h)
    simp [θ, h₁, h₂]

private lemma h_inner_diag_aux {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b c d j : ℕ) (u v w : K)
    (hbc : W.split j b c ≫ W.fuse b c j = (v / w) • 𝟙 (S.V j))
    (htheta : W.vertexUp a j d ≫ W.vertex a j d = u • 𝟙 (𝟙_ C)) :
    W.H a b c d j ≫ W.Hcov a b c d j = (u * v / w) • 𝟙 (𝟙_ C) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  simp [Vertex.H, Vertex.Hcov, monoidalComp]
  rw [← Category.assoc (S.V a ◁ (W.split j b c ▷ S.V d))
    (S.V a ◁ (W.fuse b c j ▷ S.V d))]
  rw [← whiskerLeft_comp, ← comp_whiskerRight, hbc]
  simp [htheta, smul_smul]
  congr 1
  ring

end QuantumSixJ.Network

open QuantumSixJ.Network

private theorem basis_H_inner {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C] :
    ∀ (S : SuQ2Data C) (W : Vertex S), SuQ2Axioms S → VertexNormalized W →
      ∀ a b c d j j' : ℕ,
        W.H a b c d j' ≫ W.Hcov a b c d j =
          if j' = j then ι (h a b c d j) • 𝟙 (𝟙_ C) else 0 := by
  intro S W hS hW a b c d j j'
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  by_cases hjj : j' = j
  · subst j'
    rw [if_pos rfl]
    rw [h_inner_diag_aux S W a b c d j _ _ _
      (split_fuse_normalized_aux S W hS hW b c j) (hW.theta a j d)]
    by_cases had : Admissible (a : ℤ) d j
    · by_cases hbc : Admissible (b : ℤ) c j
      · have hh : hAdmissible (a : ℤ) b c d j := ⟨had, hbc⟩
        rw [theta_swap_aux]
        simp [h, hh]
      · have hh : ¬ hAdmissible (a : ℤ) b c d j := by
          intro hh
          exact hbc hh.2
        simp [h, θ, hh, hbc]
    · have hh : ¬ hAdmissible (a : ℤ) b c d j := by
        intro hh
        exact had hh.1
      have hrot : ¬ Admissible (a : ℤ) j d := by
        intro hrot
        exact had ((admissible_swap_aux (a : ℤ) d j).mpr hrot)
      simp [h, θ, hh, hrot, had]
  · rw [if_neg hjj]
    have hbc : W.split j' b c ≫ W.fuse b c j = 0 := hS.disjoint j' j hjj _
    simp [Vertex.H, Vertex.Hcov, monoidalComp, hbc]
    rw [← Category.assoc (S.V a ◁ (W.split j' b c ▷ S.V d))
      (S.V a ◁ (W.fuse b c j ▷ S.V d))]
    rw [← whiskerLeft_comp, ← comp_whiskerRight, hbc]
    simp

namespace QuantumSixJ.Network
private lemma x_inner_diag_aux {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b c d l : ℕ) (u v w : K) (hw : w ≠ 0)
    (hab : W.split l a b ≫ W.fuse a b l = (u / w) • 𝟙 (S.V l))
    (hcd : W.split l c d ≫ W.fuse c d l = (v / w) • 𝟙 (S.V l))
    (hloop : S.cup l ≫ S.cap l = w • 𝟙 (𝟙_ C)) :
    W.X a b c d l ≫ W.Xcov a b c d l = (u * v / w) • 𝟙 (𝟙_ C) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have ht : ((u / w) • 𝟙 (S.V l)) ⊗ₘ ((v / w) • 𝟙 (S.V l)) =
      (u / w * (v / w)) • 𝟙 (S.V l ⊗ S.V l) := by
    simp [MonoidalCategory.tensorHom_def, smul_smul, mul_comm]
  simp [Vertex.X, Vertex.Xcov, monoidalComp, hab, hcd, ht, hloop, smul_smul]
  congr 1
  field_simp

end QuantumSixJ.Network
private theorem basis_X_inner {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C] :
    ∀ (S : SuQ2Data C) (W : Vertex S), SuQ2Axioms S → VertexNormalized W →
      ∀ a b c d l l' : ℕ,
        W.X a b c d l' ≫ W.Xcov a b c d l =
          if l' = l then ι (x a b c d l) • 𝟙 (𝟙_ C) else 0 := by
  intro S W hS hW a b c d l l'
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  by_cases hll : l' = l
  · subst l'
    rw [if_pos rfl]
    have hab := split_fuse_normalized_aux S W hS hW a b l
    have hcd := split_fuse_normalized_aux S W hS hW c d l
    rw [x_inner_diag_aux S W a b c d l _ _ _ (iota_delta_ne_zero_aux l)
      hab hcd (hS.loop l)]
    by_cases hab : Admissible (a : ℤ) b l
    · by_cases hcd : Admissible (c : ℤ) d l
      · have hv : vAdmissible (a : ℤ) b c d l := ⟨hab, hcd⟩
        simp [x, hv]
      · have hv : ¬ vAdmissible (a : ℤ) b c d l := by
          intro hv
          exact hcd hv.2
        simp [x, θ, hv, hcd]
    · have hv : ¬ vAdmissible (a : ℤ) b c d l := by
        intro hv
        exact hab hv.1
      simp [x, θ, hv, hab]
  · rw [if_neg hll]
    have hab : W.split l' a b ≫ W.fuse a b l = 0 := hS.disjoint l' l hll _
    have hcd : W.split l' c d ≫ W.fuse c d l = 0 := hS.disjoint l' l hll _
    simp [Vertex.X, Vertex.Xcov, monoidalComp, hab, hcd]
open CategoryTheory MonoidalCategory
open QuantumSixJ
open scoped BigOperators Classical


namespace QuantumSixJ.Network

private lemma complete_iota_ne_zero (r : Scalar) (hr : r ≠ 0) : ι r ≠ 0 := by
  apply (map_ne_zero_iff _ _).2 hr
  unfold ι
  apply RatFunc.map_injective
  · exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective)
  · exact Polynomial.map_injective _ (algebraMap ℚ ℂ).injective

private lemma complete_unit_injective {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (hS : SuQ2Axioms S) :
    Function.Injective (fun r : K => r • 𝟙 (𝟙_ C)) := by
  intro r s hrs
  have hrs0 : r • 𝟙 (S.V 0) = s • 𝟙 (S.V 0) := by
    have h := congrArg (fun f : 𝟙_ C ⟶ 𝟙_ C => S.unitIso.hom ≫ f ≫ S.unitIso.inv) hrs
    simpa [smul_smul] using h
  have hd : (0 : S.V 0 ⟶ S.V 0) = (r - s) • 𝟙 (S.V 0) := by
    rw [sub_smul, hrs0, sub_self]
  have hz : (0 : S.V 0 ⟶ S.V 0) = (0 : K) • 𝟙 (S.V 0) := by simp
  exact sub_eq_zero.mp ((hS.simple 0 0).unique hd hz)

private lemma complete_fuse_cap {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ) :
    (W.fuse a b l ▷ S.V l) ≫ S.cap l =
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let f := (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l
  have hfuse : W.fuse a b l =
      (tensorRightHomEquiv (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C)) f ≫
        (λ_ (S.V l)).hom := by
    simp [f, Vertex.fuse, tensorRightHomEquiv, monoidalComp,
      SuQ2Data.cup, SuQ2Data.cap, ExactPairing.coevaluation,
      ExactPairing.evaluation]
  rw [hfuse]
  simpa [f, tensorRightHomEquiv, monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
    ExactPairing.coevaluation, ExactPairing.evaluation, ← unitors_equal] using
    (tensorRightHomEquiv (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C)).left_inv f

private lemma complete_rotate_mates_of_rotate3 {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (a b l : ℕ)
    (f : S.V l ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C)
    (h3 : Vertex.rotate (Vertex.rotate (Vertex.rotate f)) = f) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    (tensorLeftHomEquiv (S.V l) (S.V a) (S.V a) (S.V b))
      ((tensorLeftHomEquiv
        (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C))
        (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom) =
    (tensorRightHomEquiv (S.V l) (S.V b) (S.V b) (S.V a))
      ((tensorRightHomEquiv
        (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C))
        ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
          (λ_ (S.V a)).hom) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let eLb := tensorLeftHomEquiv
    (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C)
  let eLa := tensorLeftHomEquiv
    (S.V l) (S.V a) (S.V a) (S.V b)
  let eRa := tensorRightHomEquiv
    (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)
  let eRb := tensorRightHomEquiv
    (S.V l) (S.V b) (S.V b) (S.V a)
  let close (h : S.V l ⟶ S.V a ⊗ S.V b) :
      S.V l ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C :=
    (α_ (S.V l) (S.V b) (S.V a)).inv ≫
      eRa.symm (eRb.symm h ≫ (λ_ (S.V a)).inv)
  have close_injective : Function.Injective close := by
    intro x y hxy
    apply eRb.symm.injective
    rw [← cancel_mono (λ_ (S.V a)).inv]
    apply eRa.symm.injective
    rw [← cancel_epi (α_ (S.V l) (S.V b) (S.V a)).inv]
    exact hxy
  have close_right :
      close (eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
        (λ_ (S.V a)).hom)) = f := by
    simp only [close, Equiv.symm_apply_apply, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have close_left_rotate3 :
      close (eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom)) =
        Vertex.rotate (Vertex.rotate (Vertex.rotate f)) := by
    simp [close, eLa, eLb, eRa, eRb,
      tensorLeftHomEquiv, tensorRightHomEquiv,
      Vertex.rotate, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation, monoidalComp]
    monoidal
  change
    eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom) =
      eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
        (λ_ (S.V a)).hom)
  apply close_injective
  calc
    close (eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom)) =
        Vertex.rotate (Vertex.rotate (Vertex.rotate f)) := close_left_rotate3
    _ = f := h3
    _ = close (eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
      (λ_ (S.V a)).hom)) := close_right.symm

private lemma complete_cup_split {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S)
    (hW : VertexNormalized W) (a b l : ℕ) :
    S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv (𝟙_ C) (S.V l) (S.V l) (S.V a ⊗ S.V b)
  let eLa := tensorLeftHomEquiv (S.V l) (S.V a) (S.V a) (S.V b)
  let eLb := tensorLeftHomEquiv (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C)
  let eRa := tensorRightHomEquiv (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)
  let eRb := tensorRightHomEquiv (S.V l) (S.V b) (S.V b) (S.V a)
  let r : S.V l ⟶ S.V a ⊗ S.V b :=
    eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ W.vertex l b a) ≫
      (λ_ (S.V a)).hom)
  have hsplit : W.split l a b =
      eLa (eLb (W.vertex b a l) ≫ (ρ_ (S.V b)).hom) := by
    dsimp [eLa, eLb, tensorLeftHomEquiv]
    simp only [Vertex.split, SuQ2Data.cup, ExactPairing.coevaluation]
    monoidal
  have hup : W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv =
      e ((λ_ (S.V l)).hom ≫ r) := by
    dsimp [e, r, eRa, eRb, tensorRightHomEquiv]
    simp only [Vertex.vertexUp, SuQ2Data.cup, ExactPairing.coevaluation]
    monoidal
  have hrot3 :
      Vertex.rotate (Vertex.rotate (Vertex.rotate (W.vertex l b a))) =
        W.vertex l b a := by
    rw [hW.cyclic l b a, hW.cyclic b a l, hW.cyclic a l b]
  have hm : W.split l a b = r := by
    rw [hsplit, ← hW.cyclic l b a]
    exact complete_rotate_mates_of_rotate3 S a b l (W.vertex l b a) hrot3
  calc
    S.cup l ≫ (W.split l a b ▷ S.V l) =
        e ((λ_ (S.V l)).hom ≫ W.split l a b) := by
      simp [e, tensorRightHomEquiv, SuQ2Data.cup,
        ExactPairing.coevaluation, comp_whiskerRight, unitors_equal]
    _ = e ((λ_ (S.V l)).hom ≫ r) := by rw [hm]
    _ = W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv := hup.symm

private lemma complete_closed_assembly {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ)
    (hcup : S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv)
    (hfuse : (W.fuse a b l ▷ S.V l) ≫ S.cap l =
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l) :
    S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
      W.vertexUp a b l ≫ W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc (S.cup l) (W.split l a b ▷ S.V l), hcup]
  simp only [Category.assoc]
  rw [hfuse]
  simp

private lemma complete_bubble_from_closed {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (a b l : ℕ) (u : K)
    (hclosed : S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
      u • 𝟙 (𝟙_ C)) :
    W.split l a b ≫ W.fuse a b l = (u / ι (Δ (l : ℤ))) • 𝟙 (S.V l) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  obtain ⟨s, hs, _⟩ := hS.simple l (W.split l a b ≫ W.fuse a b l)
  have hclosed' : S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
      (s * ι (Δ (l : ℤ))) • 𝟙 (𝟙_ C) := by
    rw [hs]
    simp [hS.loop, smul_smul]
  have hscalar : s * ι (Δ (l : ℤ)) = u := by
    apply complete_unit_injective S hS
    exact hclosed'.symm.trans hclosed
  have hΔ : ι (Δ (l : ℤ)) ≠ 0 := complete_iota_ne_zero _ (delta_ne_zero l (by omega))
  have hsval : s = u / ι (Δ (l : ℤ)) := (eq_div_iff hΔ).2 hscalar
  rw [← hsval]
  exact hs

private lemma complete_bubble {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (hW : VertexNormalized W)
    (hcup : ∀ a b l : ℕ, S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv)
    (a b l : ℕ) :
    W.split l a b ≫ W.fuse a b l =
      (ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ))) • 𝟙 (S.V l) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  apply complete_bubble_from_closed S W hS a b l (ι (θ (a : ℤ) b l))
  calc
    S.cup l ≫ ((W.split l a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
        W.vertexUp a b l ≫ W.vertex a b l :=
      complete_closed_assembly S W a b l (hcup a b l) (complete_fuse_cap S W a b l)
    _ = ι (θ (a : ℤ) b l) • 𝟙 (𝟙_ C) := hW.theta a b l

private lemma complete_fusion_left_scalar {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (hS : SuQ2Axioms S) (a b l : ℕ)
    (i : ∀ n, S.V n ⟶ S.V a ⊗ S.V b) (p : ∀ n, S.V a ⊗ S.V b ⟶ S.V n)
    (hi : ∀ n ∈ fusionRange a b, i n ≫ p n = 𝟙 (S.V n))
    (hpi : ∑ n ∈ fusionRange a b, p n ≫ i n = 𝟙 (S.V a ⊗ S.V b))
    (hl : l ∈ fusionRange a b) (f : S.V l ⟶ S.V a ⊗ S.V b) :
    ∃ t : K, f = t • i l := by
  have hf : f = ∑ n ∈ fusionRange a b, (f ≫ p n) ≫ i n := by
    calc
      f = f ≫ 𝟙 (S.V a ⊗ S.V b) := by simp
      _ = f ≫ ∑ n ∈ fusionRange a b, p n ≫ i n := by rw [hpi]
      _ = ∑ n ∈ fusionRange a b, (f ≫ p n) ≫ i n := by
        rw [Preadditive.comp_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Category.assoc]
  obtain ⟨t, ht, _⟩ := hS.simple l (f ≫ p l)
  refine ⟨t, ?_⟩
  rw [hf, Finset.sum_eq_single l]
  · rw [ht]
    simp
  · intro n hn hnl
    have hzero : f ≫ p n = 0 := hS.disjoint l n (Ne.symm hnl) _
    simp [hzero]
  · exact fun h => (h hl).elim

private lemma complete_fusion_right_scalar {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (hS : SuQ2Axioms S) (a b l : ℕ)
    (i : ∀ n, S.V n ⟶ S.V a ⊗ S.V b) (p : ∀ n, S.V a ⊗ S.V b ⟶ S.V n)
    (hi : ∀ n ∈ fusionRange a b, i n ≫ p n = 𝟙 (S.V n))
    (hpi : ∑ n ∈ fusionRange a b, p n ≫ i n = 𝟙 (S.V a ⊗ S.V b))
    (hl : l ∈ fusionRange a b) (f : S.V a ⊗ S.V b ⟶ S.V l) :
    ∃ t : K, f = t • p l := by
  have hf : f = ∑ n ∈ fusionRange a b, p n ≫ (i n ≫ f) := by
    calc
      f = 𝟙 (S.V a ⊗ S.V b) ≫ f := by simp
      _ = (∑ n ∈ fusionRange a b, p n ≫ i n) ≫ f := by rw [hpi]
      _ = ∑ n ∈ fusionRange a b, p n ≫ (i n ≫ f) := by
        rw [Preadditive.sum_comp]
        apply Finset.sum_congr rfl
        intro n hn
        rw [← Category.assoc]
  obtain ⟨t, ht, _⟩ := hS.simple l (i l ≫ f)
  refine ⟨t, ?_⟩
  rw [hf, Finset.sum_eq_single l]
  · rw [ht]
    simp
  · intro n hn hnl
    have hzero : i n ≫ f = 0 := hS.disjoint n l hnl _
    simp [hzero]
  · exact fun h => (h hl).elim

private lemma complete_resolution {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W)
    (hcup : ∀ a b l : ℕ, S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv)
    (a b : ℕ) :
    ∑ l ∈ fusionRange a b,
      (ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)))⁻¹ •
        (W.fuse a b l ≫ W.split l a b) = 𝟙 (S.V a ⊗ S.V b) := by
  obtain ⟨i, p, hi, hpi⟩ := hS.fusion a b
  calc
    (∑ l ∈ fusionRange a b,
      (ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)))⁻¹ •
        (W.fuse a b l ≫ W.split l a b)) = ∑ l ∈ fusionRange a b, p l ≫ i l := by
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨u, hu⟩ := complete_fusion_left_scalar S hS a b l i p hi hpi hl
        (W.split l a b)
      obtain ⟨w, hw⟩ := complete_fusion_right_scalar S hS a b l i p hi hpi hl
        (W.fuse a b l)
      have huw : u * w = ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)) := by
        apply (hS.simple l (W.split l a b ≫ W.fuse a b l)).unique
        · rw [hu, hw, Linear.smul_comp, Linear.comp_smul, hi l hl]
          simp [smul_smul]
        · exact complete_bubble S W hS hW hcup a b l
      rw [hu, hw]
      simp only [Linear.comp_smul, Linear.smul_comp, smul_smul]
      have hr : ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)) ≠ 0 := by
        apply div_ne_zero
        · exact complete_iota_ne_zero _ (theta_ne_zero _ _ _ (Finset.mem_filter.mp hl).2)
        · exact complete_iota_ne_zero _ (delta_ne_zero l (by omega))
      have hcoef : (ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)))⁻¹ * (u * w) = 1 := by
        rw [huw]
        exact inv_mul_cancel₀ hr
      rw [hcoef, one_smul]
    _ = 𝟙 (S.V a ⊗ S.V b) := hpi

private lemma complete_X_inner_diag {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b c d l : ℕ) (u v w : K) (hw : w ≠ 0)
    (hab : W.split l a b ≫ W.fuse a b l = (u / w) • 𝟙 (S.V l))
    (hcd : W.split l c d ≫ W.fuse c d l = (v / w) • 𝟙 (S.V l))
    (hloop : S.cup l ≫ S.cap l = w • 𝟙 (𝟙_ C)) :
    W.X a b c d l ≫ W.Xcov a b c d l = (u * v / w) • 𝟙 (𝟙_ C) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have ht : ((u / w) • 𝟙 (S.V l)) ⊗ₘ ((v / w) • 𝟙 (S.V l)) =
      (u / w * (v / w)) • 𝟙 (S.V l ⊗ S.V l) := by
    simp [MonoidalCategory.tensorHom_def, smul_smul, mul_comm]
  simp [Vertex.X, Vertex.Xcov, monoidalComp, hab, hcd, ht, hloop, smul_smul]
  congr 1
  field_simp

private lemma complete_X_inner {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W)
    (hcup : ∀ a b l : ℕ, S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv)
    (a b c d l l' : ℕ) :
    W.X a b c d l' ≫ W.Xcov a b c d l =
      if l' = l then ι (x (a : ℤ) b c d l) • 𝟙 (𝟙_ C) else 0 := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  by_cases hll : l' = l
  · subst l'
    rw [if_pos rfl]
    have hab := complete_bubble S W hS hW hcup a b l
    have hcd := complete_bubble S W hS hW hcup c d l
    rw [complete_X_inner_diag S W a b c d l _ _ _
      (complete_iota_ne_zero _ (delta_ne_zero l (by omega))) hab hcd (hS.loop l)]
    by_cases hab : Admissible (a : ℤ) b l
    · by_cases hcd : Admissible (c : ℤ) d l
      · have hv : vAdmissible (a : ℤ) b c d l := ⟨hab, hcd⟩
        simp [x, hv]
      · have hv : ¬ vAdmissible (a : ℤ) b c d l := by
          intro hv
          exact hcd hv.2
        simp [x, θ, hv, hcd]
    · have hv : ¬ vAdmissible (a : ℤ) b c d l := by
        intro hv
        exact hab hv.1
      simp [x, θ, hv, hab]
  · rw [if_neg hll]
    have hab : W.split l' a b ≫ W.fuse a b l = 0 := hS.disjoint l' l hll _
    have hcd : W.split l' c d ≫ W.fuse c d l = 0 := hS.disjoint l' l hll _
    simp [Vertex.X, Vertex.Xcov, monoidalComp, hab, hcd]

private lemma complete_pair_state_ne {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) (k l : ℕ) (hkl : k ≠ l)
    (q : 𝟙_ C ⟶ S.V k ⊗ S.V l) : q = 0 := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv (𝟙_ C) (S.V l) (S.V l) (S.V k)
  have hF : (λ_ (S.V l)).inv ≫ e.symm q = 0 := hS.disjoint l k (Ne.symm hkl) _
  have he : e.symm q = 0 := by
    calc
      e.symm q = (λ_ (S.V l)).hom ≫ (λ_ (S.V l)).inv ≫ e.symm q := by simp
      _ = 0 := by rw [hF]; simp
  calc
    q = e (e.symm q) := (e.right_inv q).symm
    _ = 0 := by rw [he]; simp [e, tensorRightHomEquiv]

private lemma complete_pair_state_eq {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) (l : ℕ)
    (q : 𝟙_ C ⟶ S.V l ⊗ S.V l) : ∃ t : K, q = t • S.cup l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv (𝟙_ C) (S.V l) (S.V l) (S.V l)
  let F : S.V l ⟶ S.V l := (λ_ (S.V l)).inv ≫ e.symm q
  obtain ⟨t, ht, _⟩ := hS.simple l F
  have hq : q = e ((λ_ (S.V l)).hom ≫ F) := by
    calc
      q = e (e.symm q) := (e.right_inv q).symm
      _ = e ((λ_ (S.V l)).hom ≫ F) := by simp [F]
  have hcup : e (λ_ (S.V l)).hom = S.cup l := by
    simp [e, tensorRightHomEquiv, SuQ2Data.cup, ExactPairing.coevaluation,
      ← unitors_equal]
    monoidal
  refine ⟨t, ?_⟩
  calc
    q = e ((λ_ (S.V l)).hom ≫ F) := hq
    _ = e (t • (λ_ (S.V l)).hom) := by rw [ht]; simp
    _ = t • e (λ_ (S.V l)).hom := by
      dsimp [e, tensorRightHomEquiv]
      simp
    _ = t • S.cup l := by rw [hcup]

private lemma complete_pair_covector_ne {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) (k l : ℕ) (hkl : k ≠ l)
    (q : S.V k ⊗ S.V l ⟶ 𝟙_ C) : q = 0 := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv (S.V k) (S.V l) (S.V l) (𝟙_ C)
  have hF : e q ≫ (λ_ (S.V l)).hom = 0 := hS.disjoint k l hkl _
  have he : e q = 0 := by
    calc
      e q = e q ≫ (λ_ (S.V l)).hom ≫ (λ_ (S.V l)).inv := by simp
      _ = 0 := by rw [← Category.assoc, hF]; simp
  calc
    q = e.symm (e q) := (e.left_inv q).symm
    _ = 0 := by rw [he]; simp [e, tensorRightHomEquiv]

private lemma complete_pair_covector_eq {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) (l : ℕ)
    (q : S.V l ⊗ S.V l ⟶ 𝟙_ C) : ∃ t : K, q = t • S.cap l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv (S.V l) (S.V l) (S.V l) (𝟙_ C)
  let F : S.V l ⟶ S.V l := e q ≫ (λ_ (S.V l)).hom
  obtain ⟨t, ht, _⟩ := hS.simple l F
  refine ⟨t, ?_⟩
  have hcap : e (S.cap l) = (λ_ (S.V l)).inv := by
    dsimp [e, tensorRightHomEquiv]
    change (ρ_ (S.V l)).inv ≫ S.V l ◁ η_ (S.V l) (S.V l) ≫
      (α_ (S.V l) (S.V l) (S.V l)).inv ≫ ε_ (S.V l) (S.V l) ▷ S.V l =
        (λ_ (S.V l)).inv
    rw [ExactPairing.coevaluation_evaluation]
    simp
  have heq0 : e q = t • (λ_ (S.V l)).inv := by
    calc
      e q = (e q ≫ (λ_ (S.V l)).hom) ≫ (λ_ (S.V l)).inv := by simp
      _ = (t • 𝟙 (S.V l)) ≫ (λ_ (S.V l)).inv := by rw [← ht]
      _ = t • (λ_ (S.V l)).inv := by simp
  have heq : e q = t • e (S.cap l) := by rw [hcap, heq0]
  have hsymm (z : S.V l ⟶ 𝟙_ C ⊗ S.V l) : e.symm (t • z) = t • e.symm z := by
    dsimp [e, tensorRightHomEquiv]
    simp
  calc
    q = e.symm (e q) := (e.left_inv q).symm
    _ = e.symm (t • e (S.cap l)) := by rw [heq]
    _ = t • e.symm (e (S.cap l)) := hsymm _
    _ = t • S.cap l := by
      congr 1
      exact e.left_inv _

private lemma complete_X_expand_state {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b c d : ℕ) (rab rcd : ℕ → K)
    (hresab : ∑ l ∈ fusionRange a b, (rab l)⁻¹ • (W.fuse a b l ≫ W.split l a b) =
      𝟙 (S.V a ⊗ S.V b))
    (hrescd : ∑ l ∈ fusionRange c d, (rcd l)⁻¹ • (W.fuse c d l ≫ W.split l c d) =
      𝟙 (S.V c ⊗ S.V d))
    (f : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d)
    (hpair_ne : ∀ k l : ℕ, k ≠ l → ∀ z : 𝟙_ C ⟶ S.V k ⊗ S.V l, z = 0)
    (hpair_eq : ∀ l : ℕ, ∀ z : 𝟙_ C ⟶ S.V l ⊗ S.V l, ∃ t : K, z = t • S.cup l) :
    ∃ t : ℕ → K, f = ∑ l ∈ fusionRange a b ∩ fusionRange c d,
      t l • W.X a b c d l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let R (l : ℕ) : 𝟙_ C ⟶ S.V l ⊗ (S.V c ⊗ S.V d) :=
    f ≫ (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
      (W.fuse a b l ▷ (S.V c ⊗ S.V d))
  let F (l k : ℕ) : 𝟙_ C ⟶ S.V l ⊗ S.V k := R l ≫ (S.V l ◁ W.fuse c d k)
  have hCD (l : ℕ) (z : 𝟙_ C ⟶ S.V l ⊗ (S.V c ⊗ S.V d)) :
      z = ∑ k ∈ fusionRange c d, (rcd k)⁻¹ •
        ((z ≫ (S.V l ◁ W.fuse c d k)) ≫ (S.V l ◁ W.split k c d)) := by
    calc
      z = z ≫ (S.V l ◁ 𝟙 (S.V c ⊗ S.V d)) := by simp
      _ = z ≫ (S.V l ◁ (∑ k ∈ fusionRange c d, (rcd k)⁻¹ •
          (W.fuse c d k ≫ W.split k c d))) := by rw [hrescd]
      _ = ∑ k ∈ fusionRange c d, (rcd k)⁻¹ •
          ((z ≫ (S.V l ◁ W.fuse c d k)) ≫ (S.V l ◁ W.split k c d)) := by
        simp [whiskerLeft_sum, Preadditive.comp_sum, Category.assoc]
  have hAB : f = ∑ l ∈ fusionRange a b, (rab l)⁻¹ •
      (R l ≫ (W.split l a b ▷ (S.V c ⊗ S.V d)) ≫
        (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom) := by
    calc
      f = f ≫ (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
          (𝟙 (S.V a ⊗ S.V b) ▷ (S.V c ⊗ S.V d)) ≫
          (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom := by simp
      _ = f ≫ (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
          ((∑ l ∈ fusionRange a b, (rab l)⁻¹ •
            (W.fuse a b l ≫ W.split l a b)) ▷ (S.V c ⊗ S.V d)) ≫
          (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom := by rw [hresab]
      _ = ∑ l ∈ fusionRange a b, (rab l)⁻¹ •
          (R l ≫ (W.split l a b ▷ (S.V c ⊗ S.V d)) ≫
            (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom) := by
        simp [R, sum_whiskerRight, Preadditive.comp_sum, Preadditive.sum_comp,
          comp_whiskerRight, Category.assoc]
  have hX (l : ℕ) :
      S.cup l ≫ (S.V l ◁ W.split l c d) ≫
        (W.split l a b ▷ (S.V c ⊗ S.V d)) ≫
        (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom = W.X a b c d l := by
    simp [Vertex.X, monoidalComp, MonoidalCategory.tensorHom_def', Category.assoc]
  have hf : f = ∑ l ∈ fusionRange a b, ∑ k ∈ fusionRange c d,
      ((rab l)⁻¹ * (rcd k)⁻¹) •
        (F l k ≫ (S.V l ◁ W.split k c d) ≫
          (W.split l a b ▷ (S.V c ⊗ S.V d)) ≫
          (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom) := by
    calc
      f = ∑ l ∈ fusionRange a b, (rab l)⁻¹ •
          (R l ≫ (W.split l a b ▷ (S.V c ⊗ S.V d)) ≫
            (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom) := hAB
      _ = ∑ l ∈ fusionRange a b, (rab l)⁻¹ •
          ((∑ k ∈ fusionRange c d, (rcd k)⁻¹ •
            (F l k ≫ (S.V l ◁ W.split k c d))) ≫
            (W.split l a b ▷ (S.V c ⊗ S.V d)) ≫
            (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hCD l (R l)]
      _ = ∑ l ∈ fusionRange a b, ∑ k ∈ fusionRange c d,
          ((rab l)⁻¹ * (rcd k)⁻¹) •
            (F l k ≫ (S.V l ◁ W.split k c d) ≫
              (W.split l a b ▷ (S.V c ⊗ S.V d)) ≫
              (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom) := by
        simp [Preadditive.sum_comp, Finset.smul_sum, Category.assoc, smul_smul]
  have hterm (l : ℕ) : ∃ t : K,
      (∑ k ∈ fusionRange c d, ((rab l)⁻¹ * (rcd k)⁻¹) •
        (F l k ≫ (S.V l ◁ W.split k c d) ≫
          (W.split l a b ▷ (S.V c ⊗ S.V d)) ≫
          (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom)) = t • W.X a b c d l := by
    by_cases hl : l ∈ fusionRange c d
    · obtain ⟨t, ht⟩ := hpair_eq l (F l l)
      refine ⟨(rab l)⁻¹ * (rcd l)⁻¹ * t, ?_⟩
      rw [Finset.sum_eq_single l]
      · rw [ht]
        simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
        congr 1
        simpa only [Category.assoc] using hX l
      · intro k hk hkl
        rw [hpair_ne l k (Ne.symm hkl) (F l k)]
        simp
      · exact fun h => (h hl).elim
    · refine ⟨0, ?_⟩
      simp only [zero_smul]
      apply Finset.sum_eq_zero
      intro k hk
      have hkl : k ≠ l := by
        intro h
        subst k
        exact hl hk
      rw [hpair_ne l k (Ne.symm hkl) (F l k)]
      simp
  choose t ht using hterm
  refine ⟨t, ?_⟩
  rw [hf]
  simp_rw [ht]
  symm
  apply Finset.sum_subset Finset.inter_subset_left
  intro l hlab hl
  have hlcd : l ∉ fusionRange c d := by
    intro hlcd
    exact hl (Finset.mem_inter.mpr ⟨hlab, hlcd⟩)
  rw [← ht l]
  apply Finset.sum_eq_zero
  intro k hk
  have hkl : k ≠ l := by
    intro h
    subst k
    exact hlcd hk
  rw [hpair_ne l k (Ne.symm hkl) (F l k)]
  simp

private lemma complete_X_expand_covector {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b c d : ℕ) (rab rcd : ℕ → K)
    (hresab : ∑ l ∈ fusionRange a b, (rab l)⁻¹ • (W.fuse a b l ≫ W.split l a b) =
      𝟙 (S.V a ⊗ S.V b))
    (hrescd : ∑ l ∈ fusionRange c d, (rcd l)⁻¹ • (W.fuse c d l ≫ W.split l c d) =
      𝟙 (S.V c ⊗ S.V d))
    (g : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C)
    (hpair_ne : ∀ k l : ℕ, k ≠ l → ∀ z : S.V k ⊗ S.V l ⟶ 𝟙_ C, z = 0)
    (hpair_eq : ∀ l : ℕ, ∀ z : S.V l ⊗ S.V l ⟶ 𝟙_ C, ∃ t : K, z = t • S.cap l) :
    ∃ t : ℕ → K, g = ∑ l ∈ fusionRange a b ∩ fusionRange c d,
      t l • W.Xcov a b c d l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let R (l : ℕ) : S.V l ⊗ (S.V c ⊗ S.V d) ⟶ 𝟙_ C :=
    (W.split l a b ▷ (S.V c ⊗ S.V d)) ≫
      (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom ≫ g
  let G (l k : ℕ) : S.V l ⊗ S.V k ⟶ 𝟙_ C := (S.V l ◁ W.split k c d) ≫ R l
  have hCD (l : ℕ) (z : S.V l ⊗ (S.V c ⊗ S.V d) ⟶ 𝟙_ C) :
      z = ∑ k ∈ fusionRange c d, (rcd k)⁻¹ •
        ((S.V l ◁ W.fuse c d k) ≫ ((S.V l ◁ W.split k c d) ≫ z)) := by
    calc
      z = (S.V l ◁ 𝟙 (S.V c ⊗ S.V d)) ≫ z := by simp
      _ = (S.V l ◁ (∑ k ∈ fusionRange c d, (rcd k)⁻¹ •
          (W.fuse c d k ≫ W.split k c d))) ≫ z := by rw [hrescd]
      _ = ∑ k ∈ fusionRange c d, (rcd k)⁻¹ •
          ((S.V l ◁ W.fuse c d k) ≫ ((S.V l ◁ W.split k c d) ≫ z)) := by
        simp [whiskerLeft_sum, Preadditive.sum_comp, Category.assoc]
  have hAB : g = ∑ l ∈ fusionRange a b, (rab l)⁻¹ •
      ((α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
        (W.fuse a b l ▷ (S.V c ⊗ S.V d)) ≫ R l) := by
    calc
      g = (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
          (𝟙 (S.V a ⊗ S.V b) ▷ (S.V c ⊗ S.V d)) ≫
          (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom ≫ g := by simp
      _ = (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
          ((∑ l ∈ fusionRange a b, (rab l)⁻¹ •
            (W.fuse a b l ≫ W.split l a b)) ▷ (S.V c ⊗ S.V d)) ≫
          (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).hom ≫ g := by rw [hresab]
      _ = ∑ l ∈ fusionRange a b, (rab l)⁻¹ •
          ((α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
            (W.fuse a b l ▷ (S.V c ⊗ S.V d)) ≫ R l) := by
        simp [R, sum_whiskerRight, Preadditive.comp_sum, Preadditive.sum_comp,
          comp_whiskerRight, Category.assoc]
  have hX (l : ℕ) :
      (α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
        (W.fuse a b l ▷ (S.V c ⊗ S.V d)) ≫ (S.V l ◁ W.fuse c d l) ≫ S.cap l =
          W.Xcov a b c d l := by
    simp [Vertex.Xcov, monoidalComp, MonoidalCategory.tensorHom_def, Category.assoc]
  have hg : g = ∑ l ∈ fusionRange a b, ∑ k ∈ fusionRange c d,
      ((rab l)⁻¹ * (rcd k)⁻¹) •
        ((α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
          (W.fuse a b l ▷ (S.V c ⊗ S.V d)) ≫
          (S.V l ◁ W.fuse c d k) ≫ G l k) := by
    calc
      g = ∑ l ∈ fusionRange a b, (rab l)⁻¹ •
          ((α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
            (W.fuse a b l ▷ (S.V c ⊗ S.V d)) ≫ R l) := hAB
      _ = ∑ l ∈ fusionRange a b, (rab l)⁻¹ •
          ((α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
            (W.fuse a b l ▷ (S.V c ⊗ S.V d)) ≫
            (∑ k ∈ fusionRange c d, (rcd k)⁻¹ •
              ((S.V l ◁ W.fuse c d k) ≫ G l k))) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hCD l (R l)]
      _ = ∑ l ∈ fusionRange a b, ∑ k ∈ fusionRange c d,
          ((rab l)⁻¹ * (rcd k)⁻¹) •
            ((α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
              (W.fuse a b l ▷ (S.V c ⊗ S.V d)) ≫
              (S.V l ◁ W.fuse c d k) ≫ G l k) := by
        simp [Preadditive.comp_sum, Finset.smul_sum, Category.assoc, smul_smul]
  have hterm (l : ℕ) : ∃ t : K,
      (∑ k ∈ fusionRange c d, ((rab l)⁻¹ * (rcd k)⁻¹) •
        ((α_ (S.V a) (S.V b) (S.V c ⊗ S.V d)).inv ≫
          (W.fuse a b l ▷ (S.V c ⊗ S.V d)) ≫
          (S.V l ◁ W.fuse c d k) ≫ G l k)) = t • W.Xcov a b c d l := by
    by_cases hl : l ∈ fusionRange c d
    · obtain ⟨t, ht⟩ := hpair_eq l (G l l)
      refine ⟨(rab l)⁻¹ * (rcd l)⁻¹ * t, ?_⟩
      rw [Finset.sum_eq_single l]
      · rw [ht]
        simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
        congr 1
        simpa only [Category.assoc] using hX l
      · intro k hk hkl
        rw [hpair_ne l k (Ne.symm hkl) (G l k)]
        simp
      · exact fun h => (h hl).elim
    · refine ⟨0, ?_⟩
      simp only [zero_smul]
      apply Finset.sum_eq_zero
      intro k hk
      have hkl : k ≠ l := by
        intro h
        subst k
        exact hl hk
      rw [hpair_ne l k (Ne.symm hkl) (G l k)]
      simp
  choose t ht using hterm
  refine ⟨t, ?_⟩
  rw [hg]
  simp_rw [ht]
  symm
  apply Finset.sum_subset Finset.inter_subset_left
  intro l hlab hl
  have hlcd : l ∉ fusionRange c d := by
    intro hlcd
    exact hl (Finset.mem_inter.mpr ⟨hlab, hlcd⟩)
  rw [← ht l]
  apply Finset.sum_eq_zero
  intro k hk
  have hkl : k ≠ l := by
    intro h
    subst k
    exact hlcd hk
  rw [hpair_ne l k (Ne.symm hkl) (G l k)]
  simp

private lemma complete_coeff_state {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C]
    (T : C) (basis : ∀ j : ℕ, 𝟙_ C ⟶ T) (cov : ∀ j : ℕ, T ⟶ 𝟙_ C)
    (norm : ℕ → K) (fine coarse : Finset ℕ)
    (f : 𝟙_ C ⟶ T) (t scalar : ℕ → K)
    (hsub : fine ⊆ coarse)
    (hinner : ∀ j k : ℕ, basis j ≫ cov k =
      if j = k then norm k • 𝟙 (𝟙_ C) else 0)
    (hscalar : ∀ k : ℕ, f ≫ cov k = scalar k • 𝟙 (𝟙_ C))
    (hunit : Function.Injective (fun r : K => r • 𝟙 (𝟙_ C)))
    (hnorm_ne : ∀ j ∈ fine, norm j ≠ 0)
    (hnorm_zero : ∀ j ∈ coarse, j ∉ fine → norm j = 0)
    (hf : f = ∑ j ∈ fine, t j • basis j) :
    f = ∑ j ∈ coarse, (scalar j / norm j) • basis j := by
  have ht (k : ℕ) (hk : k ∈ fine) : t k = scalar k / norm k := by
    have hp : ∑ j ∈ fine, t j • (if j = k then norm k • 𝟙 (𝟙_ C) else 0) =
        scalar k • 𝟙 (𝟙_ C) := by
      calc
        _ = (∑ j ∈ fine, t j • basis j) ≫ cov k := by
          simp [Preadditive.sum_comp, Linear.smul_comp, hinner]
        _ = f ≫ cov k := by rw [← hf]
        _ = scalar k • 𝟙 (𝟙_ C) := hscalar k
    rw [Finset.sum_eq_single k] at hp
    · apply (eq_div_iff (hnorm_ne k hk)).2
      apply hunit
      simpa only [if_pos, smul_smul] using hp
    · intro j hj hjk
      simp [hjk]
    · exact fun h => (h hk).elim
  calc
    f = ∑ j ∈ fine, t j • basis j := hf
    _ = ∑ j ∈ fine, (scalar j / norm j) • basis j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ht j hj]
    _ = ∑ j ∈ coarse, (scalar j / norm j) • basis j := by
      apply Finset.sum_subset hsub
      intro j hjcoarse hjfine
      rw [hnorm_zero j hjcoarse hjfine, div_zero, zero_smul]

private lemma complete_coeff_covector {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C]
    (T : C) (state : ∀ j : ℕ, 𝟙_ C ⟶ T) (basis : ∀ j : ℕ, T ⟶ 𝟙_ C)
    (norm : ℕ → K) (fine coarse : Finset ℕ)
    (g : T ⟶ 𝟙_ C) (t scalar : ℕ → K)
    (hsub : fine ⊆ coarse)
    (hinner : ∀ j k : ℕ, state j ≫ basis k =
      if j = k then norm k • 𝟙 (𝟙_ C) else 0)
    (hscalar : ∀ k : ℕ, state k ≫ g = scalar k • 𝟙 (𝟙_ C))
    (hunit : Function.Injective (fun r : K => r • 𝟙 (𝟙_ C)))
    (hnorm_ne : ∀ j ∈ fine, norm j ≠ 0)
    (hnorm_zero : ∀ j ∈ coarse, j ∉ fine → norm j = 0)
    (hg : g = ∑ j ∈ fine, t j • basis j) :
    g = ∑ j ∈ coarse, (scalar j / norm j) • basis j := by
  have ht (k : ℕ) (hk : k ∈ fine) : t k = scalar k / norm k := by
    have hp : ∑ j ∈ fine, t j • (if k = j then norm j • 𝟙 (𝟙_ C) else 0) =
        scalar k • 𝟙 (𝟙_ C) := by
      calc
        _ = state k ≫ ∑ j ∈ fine, t j • basis j := by
          simp [Preadditive.comp_sum, Linear.comp_smul, hinner]
        _ = state k ≫ g := by rw [← hg]
        _ = scalar k • 𝟙 (𝟙_ C) := hscalar k
    rw [Finset.sum_eq_single k] at hp
    · apply (eq_div_iff (hnorm_ne k hk)).2
      apply hunit
      simpa only [if_pos, smul_smul] using hp
    · intro j hj hjk
      have hkj : k ≠ j := Ne.symm hjk
      simp [hkj]
    · exact fun h => (h hk).elim
  calc
    g = ∑ j ∈ fine, t j • basis j := hg
    _ = ∑ j ∈ fine, (scalar j / norm j) • basis j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ht j hj]
    _ = ∑ j ∈ coarse, (scalar j / norm j) • basis j := by
      apply Finset.sum_subset hsub
      intro j hjcoarse hjfine
      rw [hnorm_zero j hjcoarse hjfine, div_zero, zero_smul]

private lemma complete_H_fusion_left_zero {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (hS : SuQ2Axioms S) (a b l : ℕ)
    (i : ∀ n, S.V n ⟶ S.V a ⊗ S.V b) (p : ∀ n, S.V a ⊗ S.V b ⟶ S.V n)
    (hpi : ∑ n ∈ fusionRange a b, p n ≫ i n = 𝟙 (S.V a ⊗ S.V b))
    (hl : l ∉ fusionRange a b) (f : S.V l ⟶ S.V a ⊗ S.V b) : f = 0 := by
  calc
    f = f ≫ 𝟙 (S.V a ⊗ S.V b) := by simp
    _ = f ≫ ∑ n ∈ fusionRange a b, p n ≫ i n := by rw [hpi]
    _ = ∑ n ∈ fusionRange a b, (f ≫ p n) ≫ i n := by
      rw [Preadditive.comp_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Category.assoc]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hln : l ≠ n := by
        intro h
        subst n
        exact hl hn
      rw [hS.disjoint l n hln (f ≫ p n)]
      simp

private lemma complete_H_fusion_right_zero {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (hS : SuQ2Axioms S) (a b l : ℕ)
    (i : ∀ n, S.V n ⟶ S.V a ⊗ S.V b) (p : ∀ n, S.V a ⊗ S.V b ⟶ S.V n)
    (hpi : ∑ n ∈ fusionRange a b, p n ≫ i n = 𝟙 (S.V a ⊗ S.V b))
    (hl : l ∉ fusionRange a b) (f : S.V a ⊗ S.V b ⟶ S.V l) : f = 0 := by
  calc
    f = 𝟙 (S.V a ⊗ S.V b) ≫ f := by simp
    _ = (∑ n ∈ fusionRange a b, p n ≫ i n) ≫ f := by rw [hpi]
    _ = ∑ n ∈ fusionRange a b, p n ≫ (i n ≫ f) := by
      rw [Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Category.assoc]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnl : n ≠ l := by
        intro h
        subst n
        exact hl hn
      rw [hS.disjoint n l hnl (i n ≫ f)]
      simp

private lemma complete_H_admissible_swap (a b c : ℤ) :
    Admissible a b c ↔ Admissible a c b := by
  constructor <;>
    rintro ⟨ha, hb, hc, h₁, h₂, h₃, h₄⟩ <;>
    refine ⟨ha, hc, hb, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma complete_H_mem_swap (a b c : ℕ) :
    c ∈ fusionRange a b ↔ b ∈ fusionRange a c := by
  simp only [fusionRange, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hbc, hadm⟩
    have htri := hadm.2.2.2.2.1
    exact ⟨by omega, (complete_H_admissible_swap (a : ℤ) b c).mp hadm⟩
  · rintro ⟨hcb, hadm⟩
    have htri := hadm.2.2.2.2.1
    exact ⟨by omega, (complete_H_admissible_swap (a : ℤ) c b).mp hadm⟩

private lemma complete_H_vertexUp_zero {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (a d j : ℕ)
    (hcup : S.cup d ≫ (W.split d a j ▷ S.V d) =
      W.vertexUp a j d ≫ (α_ (S.V a) (S.V j) (S.V d)).inv)
    (hj : j ∉ fusionRange a d) : W.vertexUp a j d = 0 := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have hd : d ∉ fusionRange a j := fun hd => hj ((complete_H_mem_swap a j d).mp hd)
  obtain ⟨i, p, hi, hpi⟩ := hS.fusion a j
  have hs : W.split d a j = 0 :=
    complete_H_fusion_left_zero S hS a j d i p hpi hd _
  apply (cancel_mono (α_ (S.V a) (S.V j) (S.V d)).inv).1
  simpa [hs] using hcup.symm

private lemma complete_H_vertex_zero {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (a d j : ℕ)
    (hcap : (W.fuse a j d ▷ S.V d) ≫ S.cap d =
      (α_ (S.V a) (S.V j) (S.V d)).hom ≫ W.vertex a j d)
    (hj : j ∉ fusionRange a d) : W.vertex a j d = 0 := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have hd : d ∉ fusionRange a j := fun hd => hj ((complete_H_mem_swap a j d).mp hd)
  obtain ⟨i, p, hi, hpi⟩ := hS.fusion a j
  have hf : W.fuse a j d = 0 :=
    complete_H_fusion_right_zero S hS a j d i p hpi hd _
  calc
    W.vertex a j d = ((α_ (S.V a) (S.V j) (S.V d)).inv ≫
        (α_ (S.V a) (S.V j) (S.V d)).hom) ≫ W.vertex a j d := by simp
    _ = (α_ (S.V a) (S.V j) (S.V d)).inv ≫
        ((α_ (S.V a) (S.V j) (S.V d)).hom ≫ W.vertex a j d) := by
      rw [Category.assoc]
    _ = (α_ (S.V a) (S.V j) (S.V d)).inv ≫
        ((W.fuse a j d ▷ S.V d) ≫ S.cap d) := by rw [hcap]
    _ = 0 := by simp [hf]

private lemma complete_H_triple_state {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ) (r : ℕ → K)
    (hres : ∑ k ∈ fusionRange a b, (r k)⁻¹ • (W.fuse a b k ≫ W.split k a b) =
      𝟙 (S.V a ⊗ S.V b))
    (hcup : S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv)
    (q : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V l)
    (hpair_ne : ∀ k : ℕ, k ≠ l → ∀ z : 𝟙_ C ⟶ S.V k ⊗ S.V l, z = 0)
    (hpair_eq : ∀ z : 𝟙_ C ⟶ S.V l ⊗ S.V l, ∃ t : K, z = t • S.cup l) :
    ∃ t : K, q = t • W.vertexUp a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let Q (k : ℕ) : 𝟙_ C ⟶ S.V k ⊗ S.V l :=
    q ≫ (α_ (S.V a) (S.V b) (S.V l)).inv ≫ (W.fuse a b k ▷ S.V l)
  have hq : q = ∑ k ∈ fusionRange a b, (r k)⁻¹ •
      (Q k ≫ (W.split k a b ▷ S.V l) ≫ (α_ (S.V a) (S.V b) (S.V l)).hom) := by
    calc
      q = q ≫ (α_ (S.V a) (S.V b) (S.V l)).inv ≫
          (𝟙 (S.V a ⊗ S.V b) ▷ S.V l) ≫ (α_ (S.V a) (S.V b) (S.V l)).hom := by simp
      _ = q ≫ (α_ (S.V a) (S.V b) (S.V l)).inv ≫
          ((∑ k ∈ fusionRange a b, (r k)⁻¹ •
            (W.fuse a b k ≫ W.split k a b)) ▷ S.V l) ≫
            (α_ (S.V a) (S.V b) (S.V l)).hom := by rw [hres]
      _ = ∑ k ∈ fusionRange a b, (r k)⁻¹ •
          (Q k ≫ (W.split k a b ▷ S.V l) ≫ (α_ (S.V a) (S.V b) (S.V l)).hom) := by
        simp [Q, sum_whiskerRight, Preadditive.comp_sum, Preadditive.sum_comp,
          comp_whiskerRight, Category.assoc]
  by_cases hl : l ∈ fusionRange a b
  · obtain ⟨t, ht⟩ := hpair_eq (Q l)
    refine ⟨t * (r l)⁻¹, ?_⟩
    rw [hq, Finset.sum_eq_single l]
    · dsimp [Q] at ht ⊢
      rw [ht]
      simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
      rw [← Category.assoc (S.cup l), hcup]
      simp [smul_smul]
      ring
    · intro k hk hkl
      rw [hpair_ne k hkl (Q k)]
      simp
    · exact fun h => (h hl).elim
  · refine ⟨0, ?_⟩
    rw [hq]
    simp only [zero_smul]
    apply Finset.sum_eq_zero
    intro k hk
    have hkl : k ≠ l := by
      intro h
      subst k
      exact hl hk
    rw [hpair_ne k hkl (Q k)]
    simp

private lemma complete_H_triple_covector {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ) (r : ℕ → K)
    (hres : ∑ k ∈ fusionRange a b, (r k)⁻¹ • (W.fuse a b k ≫ W.split k a b) =
      𝟙 (S.V a ⊗ S.V b))
    (hcap : (W.fuse a b l ▷ S.V l) ≫ S.cap l =
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l)
    (q : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C)
    (hpair_ne : ∀ k : ℕ, k ≠ l → ∀ z : S.V k ⊗ S.V l ⟶ 𝟙_ C, z = 0)
    (hpair_eq : ∀ z : S.V l ⊗ S.V l ⟶ 𝟙_ C, ∃ t : K, z = t • S.cap l) :
    ∃ t : K, q = t • W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let Q (k : ℕ) : S.V k ⊗ S.V l ⟶ 𝟙_ C :=
    (W.split k a b ▷ S.V l) ≫ (α_ (S.V a) (S.V b) (S.V l)).hom ≫ q
  have hq : q = ∑ k ∈ fusionRange a b, (r k)⁻¹ •
      ((α_ (S.V a) (S.V b) (S.V l)).inv ≫
        (W.fuse a b k ▷ S.V l) ≫ Q k) := by
    calc
      q = (α_ (S.V a) (S.V b) (S.V l)).inv ≫
          (𝟙 (S.V a ⊗ S.V b) ▷ S.V l) ≫
          (α_ (S.V a) (S.V b) (S.V l)).hom ≫ q := by simp
      _ = (α_ (S.V a) (S.V b) (S.V l)).inv ≫
          ((∑ k ∈ fusionRange a b, (r k)⁻¹ •
            (W.fuse a b k ≫ W.split k a b)) ▷ S.V l) ≫
            (α_ (S.V a) (S.V b) (S.V l)).hom ≫ q := by rw [hres]
      _ = ∑ k ∈ fusionRange a b, (r k)⁻¹ •
          ((α_ (S.V a) (S.V b) (S.V l)).inv ≫
            (W.fuse a b k ▷ S.V l) ≫ Q k) := by
        simp [Q, sum_whiskerRight, Preadditive.comp_sum, Preadditive.sum_comp,
          comp_whiskerRight, Category.assoc]
  by_cases hl : l ∈ fusionRange a b
  · obtain ⟨t, ht⟩ := hpair_eq (Q l)
    refine ⟨t * (r l)⁻¹, ?_⟩
    rw [hq, Finset.sum_eq_single l]
    · dsimp [Q] at ht ⊢
      rw [ht]
      simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
      rw [hcap]
      simp [smul_smul]
      ring
    · intro k hk hkl
      rw [hpair_ne k hkl (Q k)]
      simp
    · exact fun h => (h hl).elim
  · refine ⟨0, ?_⟩
    rw [hq]
    simp only [zero_smul]
    apply Finset.sum_eq_zero
    intro k hk
    have hkl : k ≠ l := by
      intro h
      subst k
      exact hl hk
    rw [hpair_ne k hkl (Q k)]
    simp

private lemma complete_H_expand_state {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (a b c d : ℕ) (r : ℕ → K)
    (hres : ∑ j ∈ fusionRange b c, (r j)⁻¹ • (W.fuse b c j ≫ W.split j b c) =
      𝟙 (S.V b ⊗ S.V c))
    (f : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d)
    (htriple : ∀ j : ℕ, ∀ q : 𝟙_ C ⟶ S.V a ⊗ S.V j ⊗ S.V d,
      ∃ t : K, q = t • W.vertexUp a j d)
    (hvertex_ne : ∀ j : ℕ, j ∉ fusionRange a d → W.vertexUp a j d = 0) :
    ∃ t : ℕ → K, f = ∑ j ∈ fusionRange b c ∩ fusionRange a d,
      t j • W.H a b c d j := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let R (j : ℕ) : 𝟙_ C ⟶ S.V a ⊗ S.V j ⊗ S.V d :=
    f ⊗≫ (S.V a ◁ (W.fuse b c j ▷ S.V d)) ⊗≫ 𝟙 _
  have hf : f = ∑ j ∈ fusionRange b c, (r j)⁻¹ •
      (R j ⊗≫ (S.V a ◁ (W.split j b c ▷ S.V d)) ⊗≫ 𝟙 _) := by
    calc
      f = f ⊗≫ (S.V a ◁ (𝟙 (S.V b ⊗ S.V c) ▷ S.V d)) ⊗≫ 𝟙 _ := by
        simp [monoidalComp]
      _ = f ⊗≫ (S.V a ◁ ((∑ j ∈ fusionRange b c, (r j)⁻¹ •
          (W.fuse b c j ≫ W.split j b c)) ▷ S.V d)) ⊗≫ 𝟙 _ := by rw [hres]
      _ = ∑ j ∈ fusionRange b c, (r j)⁻¹ •
          (R j ⊗≫ (S.V a ◁ (W.split j b c ▷ S.V d)) ⊗≫ 𝟙 _) := by
        simp [R, monoidalComp, sum_whiskerRight, whiskerLeft_sum,
          Preadditive.comp_sum, Preadditive.sum_comp, Finset.smul_sum,
          comp_whiskerRight, Category.assoc]
  have hterm (j : ℕ) : ∃ t : K, (r j)⁻¹ •
      (R j ⊗≫ (S.V a ◁ (W.split j b c ▷ S.V d)) ⊗≫ 𝟙 _) = t • W.H a b c d j := by
    obtain ⟨t, ht⟩ := htriple j (R j)
    refine ⟨(r j)⁻¹ * t, ?_⟩
    rw [ht]
    simp [Vertex.H, monoidalComp, Linear.smul_comp, smul_smul]
  choose t ht using hterm
  refine ⟨t, ?_⟩
  rw [hf]
  simp_rw [ht]
  symm
  apply Finset.sum_subset Finset.inter_subset_left
  intro j hjbc hj
  have hjad : j ∉ fusionRange a d := by
    intro hjad
    exact hj (Finset.mem_inter.mpr ⟨hjbc, hjad⟩)
  simp [Vertex.H, monoidalComp, hvertex_ne j hjad]

private lemma complete_H_expand_covector {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S) (a b c d : ℕ) (r : ℕ → K)
    (hres : ∑ j ∈ fusionRange b c, (r j)⁻¹ • (W.fuse b c j ≫ W.split j b c) =
      𝟙 (S.V b ⊗ S.V c))
    (g : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C)
    (htriple : ∀ j : ℕ, ∀ q : S.V a ⊗ S.V j ⊗ S.V d ⟶ 𝟙_ C,
      ∃ t : K, q = t • W.vertex a j d)
    (hvertex_ne : ∀ j : ℕ, j ∉ fusionRange a d → W.vertex a j d = 0) :
    ∃ t : ℕ → K, g = ∑ j ∈ fusionRange b c ∩ fusionRange a d,
      t j • W.Hcov a b c d j := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let R (j : ℕ) : S.V a ⊗ S.V j ⊗ S.V d ⟶ 𝟙_ C :=
    𝟙 _ ⊗≫ (S.V a ◁ (W.split j b c ▷ S.V d)) ⊗≫ g
  have hg : g = ∑ j ∈ fusionRange b c, (r j)⁻¹ •
      (𝟙 _ ⊗≫ (S.V a ◁ (W.fuse b c j ▷ S.V d)) ⊗≫ R j) := by
    calc
      g = 𝟙 _ ⊗≫ (S.V a ◁ (𝟙 (S.V b ⊗ S.V c) ▷ S.V d)) ⊗≫ g := by
        simp [monoidalComp]
      _ = 𝟙 _ ⊗≫ (S.V a ◁ ((∑ j ∈ fusionRange b c, (r j)⁻¹ •
          (W.fuse b c j ≫ W.split j b c)) ▷ S.V d)) ⊗≫ g := by rw [hres]
      _ = ∑ j ∈ fusionRange b c, (r j)⁻¹ •
          (𝟙 _ ⊗≫ (S.V a ◁ (W.fuse b c j ▷ S.V d)) ⊗≫ R j) := by
        simp [R, monoidalComp, sum_whiskerRight, whiskerLeft_sum,
          Preadditive.comp_sum, Preadditive.sum_comp, Finset.smul_sum,
          comp_whiskerRight, Category.assoc]
  have hterm (j : ℕ) : ∃ t : K, (r j)⁻¹ •
      (𝟙 _ ⊗≫ (S.V a ◁ (W.fuse b c j ▷ S.V d)) ⊗≫ R j) = t • W.Hcov a b c d j := by
    obtain ⟨t, ht⟩ := htriple j (R j)
    refine ⟨(r j)⁻¹ * t, ?_⟩
    rw [ht]
    simp [Vertex.Hcov, monoidalComp, Linear.comp_smul, smul_smul]
  choose t ht using hterm
  refine ⟨t, ?_⟩
  rw [hg]
  simp_rw [ht]
  symm
  apply Finset.sum_subset Finset.inter_subset_left
  intro j hjbc hj
  have hjad : j ∉ fusionRange a d := by
    intro hjad
    exact hj (Finset.mem_inter.mpr ⟨hjbc, hjad⟩)
  simp [Vertex.Hcov, monoidalComp, hvertex_ne j hjad]

private lemma complete_H_inter_subset (a b c d : ℕ) :
    fusionRange b c ∩ fusionRange a d ⊆ Finset.range (b + c + 1) := by
  intro j hj
  exact Finset.filter_subset _ _ (Finset.mem_inter.mp hj).1

private lemma complete_H_norm_ne (a b c d j : ℕ)
    (hj : j ∈ fusionRange b c ∩ fusionRange a d) :
    ι (h (a : ℤ) b c d j) ≠ 0 := by
  apply complete_iota_ne_zero
  apply h_ne_zero
  exact ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2,
    (Finset.mem_filter.mp (Finset.mem_inter.mp hj).1).2⟩

private lemma complete_H_norm_zero (a b c d j : ℕ)
    (hjcoarse : j ∈ Finset.range (b + c + 1))
    (hjfine : j ∉ fusionRange b c ∩ fusionRange a d) :
    ι (h (a : ℤ) b c d j) = 0 := by
  have hbad : ¬ hAdmissible (a : ℤ) b c d j := by
    rintro ⟨had, hbc⟩
    apply hjfine
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      have htri := hbc.2.2.2.2.2.1
      exact ⟨Finset.mem_range.mpr (by omega), hbc⟩
    · apply Finset.mem_filter.mpr
      have htri := had.2.2.2.2.2.1
      exact ⟨Finset.mem_range.mpr (by omega), had⟩
  simp [h, hbad]

end QuantumSixJ.Network

open QuantumSixJ.Network

private theorem basis_H_complete {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C] :
    ∀ (S : SuQ2Data C) (W : Vertex S), SuQ2Axioms S → VertexNormalized W →
      ∀ a b c d : ℕ,
        (∀ (f : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d) (s : ℕ → K),
          (∀ j : ℕ, f ≫ W.Hcov a b c d j = s j • 𝟙 (𝟙_ C)) →
          f = ∑ j ∈ Finset.range (b + c + 1),
            (s j / ι (h a b c d j)) • W.H a b c d j) ∧
        (∀ (g : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C) (s : ℕ → K),
          (∀ j : ℕ, W.H a b c d j ≫ g = s j • 𝟙 (𝟙_ C)) →
          g = ∑ j ∈ Finset.range (b + c + 1),
            (s j / ι (h a b c d j)) • W.Hcov a b c d j) := by
  intro S W hS hW a b c d
  have hcup := complete_cup_split S W hW
  constructor
  · intro f s hs
    obtain ⟨t, hf⟩ := complete_H_expand_state S W a b c d
      (fun j => ι (θ (b : ℤ) c j) / ι (Δ (j : ℤ)))
      (complete_resolution S W hS hW hcup b c) f
      (fun j q => complete_H_triple_state S W a j d
        (fun k => ι (θ (a : ℤ) j k) / ι (Δ (k : ℤ)))
        (complete_resolution S W hS hW hcup a j) (hcup a j d) q
        (fun k hkd z => complete_pair_state_ne S hS k d hkd z)
        (fun z => complete_pair_state_eq S hS d z))
      (fun j hj => complete_H_vertexUp_zero S W hS a d j (hcup a j d) hj)
    apply complete_coeff_state (S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d)
      (fun j => W.H a b c d j) (fun j => W.Hcov a b c d j)
      (fun j => ι (h a b c d j))
      (fusionRange b c ∩ fusionRange a d) (Finset.range (b + c + 1)) f t s
    · exact complete_H_inter_subset a b c d
    · intro j k
      exact basis_H_inner S W hS hW a b c d k j
    · exact hs
    · exact complete_unit_injective S hS
    · intro j hj
      exact complete_H_norm_ne a b c d j hj
    · intro j hjcoarse hjfine
      exact complete_H_norm_zero a b c d j hjcoarse hjfine
    · exact hf
  · intro g s hs
    obtain ⟨t, hg⟩ := complete_H_expand_covector S W a b c d
      (fun j => ι (θ (b : ℤ) c j) / ι (Δ (j : ℤ)))
      (complete_resolution S W hS hW hcup b c) g
      (fun j q => complete_H_triple_covector S W a j d
        (fun k => ι (θ (a : ℤ) j k) / ι (Δ (k : ℤ)))
        (complete_resolution S W hS hW hcup a j) (complete_fuse_cap S W a j d) q
        (fun k hkd z => complete_pair_covector_ne S hS k d hkd z)
        (fun z => complete_pair_covector_eq S hS d z))
      (fun j hj => complete_H_vertex_zero S W hS a d j (complete_fuse_cap S W a j d) hj)
    apply complete_coeff_covector (S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d)
      (fun j => W.H a b c d j) (fun j => W.Hcov a b c d j)
      (fun j => ι (h a b c d j))
      (fusionRange b c ∩ fusionRange a d) (Finset.range (b + c + 1)) g t s
    · exact complete_H_inter_subset a b c d
    · intro j k
      exact basis_H_inner S W hS hW a b c d k j
    · exact hs
    · exact complete_unit_injective S hS
    · intro j hj
      exact complete_H_norm_ne a b c d j hj
    · intro j hjcoarse hjfine
      exact complete_H_norm_zero a b c d j hjcoarse hjfine
    · exact hg

namespace QuantumSixJ.Network
private lemma complete_X_inter_subset (a b c d : ℕ) :
    fusionRange a b ∩ fusionRange c d ⊆ Finset.range (a + b + 1) := by
  intro l hl
  exact Finset.filter_subset _ _ (Finset.mem_inter.mp hl).1

private lemma complete_X_norm_ne (a b c d l : ℕ)
    (hl : l ∈ fusionRange a b ∩ fusionRange c d) :
    ι (x (a : ℤ) b c d l) ≠ 0 := by
  apply complete_iota_ne_zero
  apply x_ne_zero
  exact ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hl).1).2,
    (Finset.mem_filter.mp (Finset.mem_inter.mp hl).2).2⟩

private lemma complete_X_norm_zero (a b c d l : ℕ)
    (hlcoarse : l ∈ Finset.range (a + b + 1))
    (hlfine : l ∉ fusionRange a b ∩ fusionRange c d) :
    ι (x (a : ℤ) b c d l) = 0 := by
  have hbad : ¬ vAdmissible (a : ℤ) b c d l := by
    rintro ⟨hab, hcd⟩
    apply hlfine
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      have htri := hab.2.2.2.2.2.1
      exact ⟨Finset.mem_range.mpr (by omega), hab⟩
    · apply Finset.mem_filter.mpr
      have htri := hcd.2.2.2.2.2.1
      exact ⟨Finset.mem_range.mpr (by omega), hcd⟩
  simp [x, hbad]

end QuantumSixJ.Network
private theorem basis_X_complete {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C] :
    ∀ (S : SuQ2Data C) (W : Vertex S), SuQ2Axioms S → VertexNormalized W →
      ∀ a b c d : ℕ,
        (∀ (f : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d) (s : ℕ → K),
          (∀ l : ℕ, f ≫ W.Xcov a b c d l = s l • 𝟙 (𝟙_ C)) →
          f = ∑ l ∈ Finset.range (a + b + 1),
            (s l / ι (x (a : ℤ) b c d l)) • W.X a b c d l) ∧
        (∀ (g : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C) (s : ℕ → K),
          (∀ l : ℕ, W.X a b c d l ≫ g = s l • 𝟙 (𝟙_ C)) →
          g = ∑ l ∈ Finset.range (a + b + 1),
            (s l / ι (x (a : ℤ) b c d l)) • W.Xcov a b c d l) := by
  intro S W hS hW a b c d
  have hcup := complete_cup_split S W hW
  constructor
  · intro f s hs
    obtain ⟨t, hf⟩ := complete_X_expand_state S W a b c d
      (fun l => ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)))
      (fun l => ι (θ (c : ℤ) d l) / ι (Δ (l : ℤ)))
      (complete_resolution S W hS hW hcup a b)
      (complete_resolution S W hS hW hcup c d) f
      (fun k l hkl z => complete_pair_state_ne S hS k l hkl z)
      (fun l z => complete_pair_state_eq S hS l z)
    apply complete_coeff_state (S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d)
      (fun l => W.X a b c d l) (fun l => W.Xcov a b c d l)
      (fun l => ι (x (a : ℤ) b c d l))
      (fusionRange a b ∩ fusionRange c d) (Finset.range (a + b + 1)) f t s
    · exact complete_X_inter_subset a b c d
    · intro j k
      exact basis_X_inner S W hS hW a b c d k j
    · exact hs
    · exact complete_unit_injective S hS
    · intro l hl
      exact complete_X_norm_ne a b c d l hl
    · intro l hlcoarse hlfine
      exact complete_X_norm_zero a b c d l hlcoarse hlfine
    · exact hf
  · intro g s hs
    obtain ⟨t, hg⟩ := complete_X_expand_covector S W a b c d
      (fun l => ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ)))
      (fun l => ι (θ (c : ℤ) d l) / ι (Δ (l : ℤ)))
      (complete_resolution S W hS hW hcup a b)
      (complete_resolution S W hS hW hcup c d) g
      (fun k l hkl z => complete_pair_covector_ne S hS k l hkl z)
      (fun l z => complete_pair_covector_eq S hS l z)
    apply complete_coeff_covector (S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d)
      (fun l => W.X a b c d l) (fun l => W.Xcov a b c d l)
      (fun l => ι (x (a : ℤ) b c d l))
      (fusionRange a b ∩ fusionRange c d) (Finset.range (a + b + 1)) g t s
    · exact complete_X_inter_subset a b c d
    · intro j k
      exact basis_X_inner S W hS hW a b c d k j
    · exact hs
    · exact complete_unit_injective S hS
    · intro l hl
      exact complete_X_norm_ne a b c d l hl
    · intro l hlcoarse hlfine
      exact complete_X_norm_zero a b c d l hlcoarse hlfine
    · exact hg

namespace QuantumSixJ.Network
private lemma basis_unit_scalar {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) (f : 𝟙_ C ⟶ 𝟙_ C) :
    ∃ s : K, f = s • 𝟙 (𝟙_ C) := by
  obtain ⟨s, hs, _⟩ := hS.simple 0 (S.unitIso.hom ≫ f ≫ S.unitIso.inv)
  refine ⟨s, ?_⟩
  have hh := congrArg (fun z => S.unitIso.inv ≫ z ≫ S.unitIso.hom) hs
  simpa using hh
end QuantumSixJ.Network

open QuantumSixJ.Network

private theorem basis_six {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W) :
    ∀ a b c d : ℕ,
      (∀ j k : ℕ, W.H a b c d k ≫ W.Hcov a b c d j =
        if k = j then ι (h a b c d j) • 𝟙 (𝟙_ C) else 0) ∧
      (∀ l m : ℕ, W.X a b c d m ≫ W.Xcov a b c d l =
        if m = l then ι (x a b c d l) • 𝟙 (𝟙_ C) else 0) ∧
      (∀ f : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d,
        ∃ s : ℕ → K,
          (∀ j : ℕ, f ≫ W.Hcov a b c d j = s j • 𝟙 (𝟙_ C)) ∧
          f = ∑ j ∈ Finset.range (b + c + 1), (s j / ι (h a b c d j)) • W.H a b c d j) ∧
      (∀ g : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C,
        ∃ s : ℕ → K,
          (∀ j : ℕ, W.H a b c d j ≫ g = s j • 𝟙 (𝟙_ C)) ∧
          g = ∑ j ∈ Finset.range (b + c + 1), (s j / ι (h a b c d j)) • W.Hcov a b c d j) ∧
      (∀ f : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d,
        ∃ s : ℕ → K,
          (∀ l : ℕ, f ≫ W.Xcov a b c d l = s l • 𝟙 (𝟙_ C)) ∧
          f = ∑ l ∈ Finset.range (a + b + 1), (s l / ι (x a b c d l)) • W.X a b c d l) ∧
      (∀ g : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C,
        ∃ s : ℕ → K,
          (∀ l : ℕ, W.X a b c d l ≫ g = s l • 𝟙 (𝟙_ C)) ∧
          g = ∑ l ∈ Finset.range (a + b + 1), (s l / ι (x a b c d l)) • W.Xcov a b c d l) := by
  classical
  intro a b c d
  have hH := basis_H_complete S W hS hW a b c d
  have hX := basis_X_complete S W hS hW a b c d
  refine ⟨basis_H_inner S W hS hW a b c d,
    basis_X_inner S W hS hW a b c d, ?_, ?_, ?_, ?_⟩
  · intro f
    choose s hs using fun j => basis_unit_scalar S hS (f ≫ W.Hcov a b c d j)
    exact ⟨s, hs, hH.1 f s hs⟩
  · intro g
    choose s hs using fun j => basis_unit_scalar S hS (W.H a b c d j ≫ g)
    exact ⟨s, hs, hH.2 g s hs⟩
  · intro f
    choose s hs using fun l => basis_unit_scalar S hS (f ≫ W.Xcov a b c d l)
    exact ⟨s, hs, hX.1 f s hs⟩
  · intro g
    choose s hs using fun l => basis_unit_scalar S hS (W.X a b c d l ≫ g)
    exact ⟨s, hs, hX.2 g s hs⟩

open CategoryTheory MonoidalCategory
namespace QuantumSixJ.Network
set_option maxRecDepth 8192
private def rungFuse {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (S : SuQ2Data C) {a b l : ℕ}
    (f : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C) : S.V a ⊗ S.V b ⟶ S.V l :=
  𝟙 _ ⊗≫ ((S.V a ⊗ S.V b) ◁ S.cup l) ⊗≫ (f ▷ S.V l) ⊗≫ 𝟙 _

private lemma rungFuse_mate {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b l : ℕ)
    (f : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    rungFuse S f =
      (tensorRightHomEquiv
        (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C))
        ((α_ (S.V a) (S.V b) (S.V l)).hom ≫ f) ≫
          (λ_ (S.V l)).hom := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  simp [rungFuse, tensorRightHomEquiv, monoidalComp,
    SuQ2Data.cup, SuQ2Data.cap, ExactPairing.coevaluation,
    ExactPairing.evaluation]

private lemma rungFuse_cap {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b l : ℕ)
    (g : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C) :
    (rungFuse S g ▷ S.V l) ≫ S.cap l =
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ g := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv
    (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C)
  rw [rungFuse_mate]
  simpa [e, tensorRightHomEquiv, monoidalComp, SuQ2Data.cup,
    SuQ2Data.cap, ExactPairing.coevaluation, ExactPairing.evaluation,
    ← unitors_equal] using
    e.left_inv ((α_ (S.V a) (S.V b) (S.V l)).hom ≫ g)

/-- A rotation converts the right mate defining `rungFuse` to a left mate. -/
private lemma rungRotate_mate {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b l : ℕ)
    (f : S.V l ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    (tensorRightHomEquiv
      (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C))
      ((α_ (S.V b) (S.V a) (S.V l)).hom ≫ Vertex.rotate f) =
      (((tensorLeftHomEquiv
        (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C)) f ≫
          (ρ_ (S.V l)).hom) ≫ (λ_ (S.V l)).inv) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let eL := tensorLeftHomEquiv
    (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C)
  let eR := tensorRightHomEquiv
    (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C)
  let q : S.V b ⊗ S.V a ⟶ 𝟙_ C ⊗ S.V l :=
    (eL f ≫ (ρ_ (S.V l)).hom) ≫ (λ_ (S.V l)).inv
  have hrotate :
      (α_ (S.V b) (S.V a) (S.V l)).hom ≫ Vertex.rotate f =
        eR.symm q := by
    dsimp [eR, eL, q, tensorRightHomEquiv, tensorLeftHomEquiv]
    simp only [Vertex.rotate, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation]
    monoidal
  change eR ((α_ (S.V b) (S.V a) (S.V l)).hom ≫ Vertex.rotate f) = q
  calc
    _ = eR (eR.symm q) := by rw [hrotate]
    _ = q := eR.right_inv q

lemma basis_leftcap {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W) (a b c : ℕ) :
    (S.V a ◁ W.fuse b c a) ≫ S.cap a = W.vertex a b c := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorLeftHomEquiv (S.V b ⊗ S.V c) (S.V a) (S.V a) (𝟙_ C)
  have hm := rungRotate_mate S c b a (W.vertex a b c)
  rw [hW.cyclic a b c] at hm
  have hfuse : W.fuse b c a = e (W.vertex a b c) ≫ (ρ_ (S.V a)).hom := by
    change rungFuse S (W.vertex b c a) = _
    rw [rungFuse_mate, hm]
    simp [e]
  rw [hfuse]
  have hu : (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
    rw [unitors_equal]
    simp
  simpa [e, tensorLeftHomEquiv, monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
    ExactPairing.coevaluation, ExactPairing.evaluation, hu, ← unitors_equal] using
      e.left_inv (W.vertex a b c)

lemma basis_rightcup {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W) (a b c : ℕ) :
    S.cup a ≫ (S.V a ◁ W.split a b c) = W.vertexUp a b c := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e1 := tensorRightHomEquiv (𝟙_ C) (S.V c) (S.V c) (S.V a ⊗ S.V b)
  let e2 := tensorRightHomEquiv (S.V c) (S.V b) (S.V b) (S.V a)
  let e3 := tensorRightHomEquiv (S.V c ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)
  let close (q : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c) :
      S.V c ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C :=
    (α_ (S.V c) (S.V b) (S.V a)).inv ≫
      e3.symm (e2.symm ((λ_ (S.V c)).inv ≫
        e1.symm (q ≫ (α_ (S.V a) (S.V b) (S.V c)).inv)) ≫ (λ_ (S.V a)).inv)
  have hinj : Function.Injective close := by
    intro x y hxy
    rw [← cancel_mono (α_ (S.V a) (S.V b) (S.V c)).inv]
    apply e1.symm.injective
    rw [← cancel_epi (λ_ (S.V c)).inv]
    apply e2.symm.injective
    rw [← cancel_mono (λ_ (S.V a)).inv]
    apply e3.symm.injective
    rw [← cancel_epi (α_ (S.V c) (S.V b) (S.V a)).inv]
    exact hxy
  have hup : W.vertexUp a b c =
      e1 ((λ_ (S.V c)).hom ≫
        e2 (e3 ((α_ (S.V c) (S.V b) (S.V a)).hom ≫ W.vertex c b a) ≫
          (λ_ (S.V a)).hom)) ≫ (α_ (S.V a) (S.V b) (S.V c)).hom := by
    simp [e1, e2, e3, tensorRightHomEquiv, Vertex.vertexUp, monoidalComp,
      SuQ2Data.cup, ExactPairing.coevaluation]
    all_goals monoidal
  have hcUp : close (W.vertexUp a b c) = W.vertex c b a := by
    rw [hup]
    simp [close]
  have hcCup : close (S.cup a ≫ (S.V a ◁ W.split a b c)) =
      Vertex.rotate (Vertex.rotate (Vertex.rotate (W.vertex c b a))) := by
    simp [close, e1, e2, e3, tensorRightHomEquiv, Vertex.split,
      Vertex.rotate, monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation]
    all_goals monoidal
  apply hinj
  rw [hcCup, hcUp, hW.cyclic c b a, hW.cyclic b a c, hW.cyclic a c b]

section Overlap
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]

private noncomputable def pairCup {A A' B B' : C}
    (ca : 𝟙_ C ⟶ A ⊗ A') (cb : 𝟙_ C ⟶ B ⊗ B') :
    𝟙_ C ⟶ (A ⊗ B) ⊗ (B' ⊗ A') :=
  ca ⊗≫ (A ◁ cb ▷ A') ⊗≫ 𝟙 _

private lemma cup_comp {A A' B B' D D' : C}
    (ca : 𝟙_ C ⟶ A ⊗ A') (cb : 𝟙_ C ⟶ B ⊗ B')
    (cd : 𝟙_ C ⟶ D ⊗ D')
    (f : A ⟶ B) (ft : B' ⟶ A') (g : B ⟶ D) (gt : D' ⟶ B')
    (hf : ca ≫ (f ▷ A') = cb ≫ (B ◁ ft))
    (hg : cb ≫ (g ▷ B') = cd ≫ (D ◁ gt)) :
    ca ≫ ((f ≫ g) ▷ A') = cd ≫ (D ◁ (gt ≫ ft)) := by
  calc
    _ = ca ≫ (f ▷ A') ≫ (g ▷ A') := by simp
    _ = cb ≫ (B ◁ ft) ≫ (g ▷ A') := by
      rw [← Category.assoc, hf]; simp only [Category.assoc]
    _ = cb ≫ (g ▷ B') ≫ (D ◁ ft) := by rw [whisker_exchange]
    _ = cd ≫ (D ◁ gt) ≫ (D ◁ ft) := by
      rw [← Category.assoc, hg]; simp only [Category.assoc]
    _ = _ := by simp

private lemma cup_left {A A' B B' D D' : C}
    (ca : 𝟙_ C ⟶ A ⊗ A') (cb : 𝟙_ C ⟶ B ⊗ B')
    (cd : 𝟙_ C ⟶ D ⊗ D') (f : B ⟶ D) (ft : D' ⟶ B')
    (hf : cb ≫ (f ▷ B') = cd ≫ (D ◁ ft)) :
    pairCup ca cb ≫ ((A ◁ f) ▷ (B' ⊗ A')) =
      pairCup ca cd ≫ ((A ⊗ D) ◁ (ft ▷ A')) := by
  calc
    _ = ca ⊗≫ (A ◁ ((cb ≫ (f ▷ B')) ▷ A')) ⊗≫ 𝟙 _ := by
      dsimp [pairCup]; monoidal
    _ = ca ⊗≫ (A ◁ ((cd ≫ (D ◁ ft)) ▷ A')) ⊗≫ 𝟙 _ := by rw [hf]
    _ = _ := by dsimp [pairCup]; monoidal

private lemma cup_right {A A' B B' D D' : C}
    (ca : 𝟙_ C ⟶ A ⊗ A') (cb : 𝟙_ C ⟶ B ⊗ B')
    (cd : 𝟙_ C ⟶ D ⊗ D') (f : A ⟶ D) (ft : D' ⟶ A')
    (hf : ca ≫ (f ▷ A') = cd ≫ (D ◁ ft)) :
    pairCup ca cb ≫ ((f ▷ B) ▷ (B' ⊗ A')) =
      pairCup cd cb ≫ ((D ⊗ B) ◁ (B' ◁ ft)) := by
  have hx : (A ◁ cb) ≫ (f ▷ (B ⊗ B')) = (f ▷ (𝟙_ C)) ≫ (D ◁ cb) := by
    rw [whisker_exchange]
  have hy : ((𝟙_ C) ◁ ft) ≫ (cb ▷ A') =
      (cb ▷ D') ≫ ((B ⊗ B') ◁ ft) := by rw [whisker_exchange]
  calc
    _ = ca ⊗≫ (((A ◁ cb) ≫ (f ▷ (B ⊗ B'))) ▷ A') ⊗≫ 𝟙 _ := by
      dsimp [pairCup]; monoidal
    _ = ca ⊗≫ (((f ▷ (𝟙_ C)) ≫ (D ◁ cb)) ▷ A') ⊗≫ 𝟙 _ := by rw [hx]
    _ = (ca ≫ (f ▷ A')) ⊗≫ (D ◁ cb ▷ A') ⊗≫ 𝟙 _ := by monoidal
    _ = (cd ≫ (D ◁ ft)) ⊗≫ (D ◁ cb ▷ A') ⊗≫ 𝟙 _ := by rw [hf]
    _ = cd ⊗≫ (D ◁ (((𝟙_ C) ◁ ft) ≫ (cb ▷ A'))) ⊗≫ 𝟙 _ := by monoidal
    _ = cd ⊗≫ (D ◁ ((cb ▷ D') ≫ ((B ⊗ B') ◁ ft))) ⊗≫ 𝟙 _ := by rw [hy]
    _ = _ := by dsimp [pairCup]; monoidal

private lemma split_bend (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (l a b : ℕ) :
    W.split l a b = 𝟙 _ ⊗≫ (S.cup a ▷ S.V l) ⊗≫ (S.V a ◁ W.fuse a l b) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have hm := rungRotate_mate S l a b (W.vertex b a l)
  rw [hW.cyclic b a l] at hm
  have hfuse : W.fuse a l b =
      (tensorLeftHomEquiv (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C))
        (W.vertex b a l) ≫ (ρ_ (S.V b)).hom := by
    change rungFuse S (W.vertex a l b) = _
    rw [rungFuse_mate, hm]
    simp
  rw [hfuse]
  simp [Vertex.split, tensorLeftHomEquiv, monoidalComp, SuQ2Data.cup,
    ExactPairing.coevaluation]
  all_goals monoidal

private lemma split_cup (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (l a b : ℕ) :
    S.cup l ≫ (W.split l a b ▷ S.V l) =
      pairCup (S.cup a) (S.cup b) ≫ ((S.V a ⊗ S.V b) ◁ W.fuse b a l) := by
  rw [pivot2_cup_split S W hW]
  rw [← basis_rightcup S W hW a b l, split_bend S W hW a b l]
  dsimp [pairCup]
  monoidal

private lemma fuse_cup (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (a b l : ℕ) :
    pairCup (S.cup a) (S.cup b) ≫ (W.fuse a b l ▷ (S.V b ⊗ S.V a)) =
      S.cup l ≫ (S.V l ◁ W.split l b a) := by
  rw [basis_rightcup S W hW l b a]
  simp [pairCup, Vertex.fuse, Vertex.vertexUp, monoidalComp,
    SuQ2Data.cup, ExactPairing.coevaluation]
  all_goals monoidal

private lemma cup_assoc {A A' B B' D D' : C}
    (ca : 𝟙_ C ⟶ A ⊗ A') (cb : 𝟙_ C ⟶ B ⊗ B')
    (cd : 𝟙_ C ⟶ D ⊗ D') :
    pairCup ca (pairCup cb cd) ≫ ((α_ A B D).inv ▷ ((D' ⊗ B') ⊗ A')) =
      pairCup (pairCup ca cb) cd ≫ (((A ⊗ B) ⊗ D) ◁ (α_ D' B' A').inv) := by
  dsimp [pairCup]
  monoidal

private noncomputable def tetCut (S : SuQ2Data C) (W : Vertex S)
    (a b c d j l : ℕ) : S.V a ⟶ S.V a :=
  W.split a b l ≫ (S.V b ◁ W.split l c d) ≫
    (α_ (S.V b) (S.V c) (S.V d)).inv ≫
      (W.fuse b c j ▷ S.V d) ≫ W.fuse j d a

private lemma cut_cup (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (a b c d j l : ℕ) :
    S.cup a ≫ (tetCut S W a b c d j l ▷ S.V a) =
      S.cup a ≫ (S.V a ◁ tetCut S W a d c b l j) := by
  have h1 := split_cup S W hW a b l
  have h2 := cup_left (S.cup b) (S.cup l)
    (pairCup (S.cup c) (S.cup d)) (W.split l c d) (W.fuse d c l)
    (split_cup S W hW l c d)
  have h2a := cup_comp
    (pairCup (S.cup b) (S.cup l))
    (pairCup (S.cup b) (pairCup (S.cup c) (S.cup d)))
    (pairCup (pairCup (S.cup b) (S.cup c)) (S.cup d))
    (S.V b ◁ W.split l c d) (W.fuse d c l ▷ S.V b)
    (α_ (S.V b) (S.V c) (S.V d)).inv
    (α_ (S.V d) (S.V c) (S.V b)).inv h2
    (cup_assoc (S.cup b) (S.cup c) (S.cup d))
  have h3 := cup_right (pairCup (S.cup b) (S.cup c)) (S.cup d) (S.cup j)
    (W.fuse b c j) (W.split j c b) (fuse_cup S W hW b c j)
  have h4 := fuse_cup S W hW j d a
  have h12 := cup_comp (S.cup a) (pairCup (S.cup b) (S.cup l))
    (pairCup (pairCup (S.cup b) (S.cup c)) (S.cup d))
    (W.split a b l) (W.fuse l b a)
    ((S.V b ◁ W.split l c d) ≫ (α_ (S.V b) (S.V c) (S.V d)).inv)
    ((α_ (S.V d) (S.V c) (S.V b)).inv ≫ (W.fuse d c l ▷ S.V b)) h1 h2a
  have h123 := cup_comp (S.cup a)
    (pairCup (pairCup (S.cup b) (S.cup c)) (S.cup d))
    (pairCup (S.cup j) (S.cup d))
    (W.split a b l ≫ ((S.V b ◁ W.split l c d) ≫
      (α_ (S.V b) (S.V c) (S.V d)).inv))
    (((α_ (S.V d) (S.V c) (S.V b)).inv ≫ (W.fuse d c l ▷ S.V b)) ≫
      W.fuse l b a)
    (W.fuse b c j ▷ S.V d) (S.V d ◁ W.split j c b) h12 h3
  have h1234 := cup_comp (S.cup a) (pairCup (S.cup j) (S.cup d)) (S.cup a)
    ((W.split a b l ≫ ((S.V b ◁ W.split l c d) ≫
      (α_ (S.V b) (S.V c) (S.V d)).inv)) ≫ (W.fuse b c j ▷ S.V d))
    ((S.V d ◁ W.split j c b) ≫
      (((α_ (S.V d) (S.V c) (S.V b)).inv ≫ (W.fuse d c l ▷ S.V b)) ≫ W.fuse l b a))
    (W.fuse j d a) (W.split a d j) h123 h4
  simpa only [tetCut, Category.assoc] using h1234

private lemma cut_trace (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (a b c d j l : ℕ) :
    S.cup a ≫ (S.V a ◁ tetCut S W a b c d j l) ≫ S.cap a =
      W.X a b c d l ≫ W.Hcov a b c d j := by
  simp only [tetCut, whiskerLeft_comp, Category.assoc]
  rw [basis_leftcap S W hW a j d]
  rw [← Category.assoc (S.cup a) (S.V a ◁ W.split a b l), basis_rightcup S W hW]
  simp [Vertex.X, Vertex.Hcov, monoidalComp, MonoidalCategory.tensorHom_def]
  rw [← Category.assoc (S.cup l) (W.split l a b ▷ S.V l),
    pivot2_cup_split S W hW]
  monoidal

lemma basis_overlap (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (hW : VertexNormalized W) (a b c d j l : ℕ) :
    W.X a b c d l ≫ W.Hcov a b c d j = W.tet a b c d j l := by
  have hs := congrArg (fun z : 𝟙_ C ⟶ S.V a ⊗ S.V a => z ≫ S.cap a)
    (cut_cup S W hW a b c d j l)
  have ht : S.cup a ≫ (S.V a ◁ tetCut S W a b c d j l) ≫ S.cap a =
      S.cup a ≫ (tetCut S W a b c d j l ▷ S.V a) ≫ S.cap a := by
    obtain ⟨s, he, _⟩ := hS.simple a (tetCut S W a b c d j l)
    rw [he]
    simp
  calc
    _ = S.cup a ≫ (S.V a ◁ tetCut S W a b c d j l) ≫ S.cap a :=
      (cut_trace S W hW a b c d j l).symm
    _ = S.cup a ≫ (tetCut S W a b c d j l ▷ S.V a) ≫ S.cap a := ht
    _ = S.cup a ≫ (S.V a ◁ tetCut S W a d c b l j) ≫ S.cap a := by
      simpa only [Category.assoc] using hs
    _ = W.X a d c b j ≫ W.Hcov a d c b l := cut_trace S W hW a d c b l j
    _ = W.tet a b c d j l := by
      simp [Vertex.tet]

end Overlap

end QuantumSixJ.Network

theorem solution {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W) :
    ∀ a b c d : ℕ,
      (∀ j k : ℕ, W.H a b c d k ≫ W.Hcov a b c d j =
        if k = j then ι (h a b c d j) • 𝟙 (𝟙_ C) else 0) ∧
      (∀ l m : ℕ, W.X a b c d m ≫ W.Xcov a b c d l =
        if m = l then ι (x a b c d l) • 𝟙 (𝟙_ C) else 0) ∧
      (∀ f : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d,
        ∃ s : ℕ → K,
          (∀ j : ℕ, f ≫ W.Hcov a b c d j = s j • 𝟙 (𝟙_ C)) ∧
          f = ∑ j ∈ Finset.range (b + c + 1), (s j / ι (h a b c d j)) • W.H a b c d j) ∧
      (∀ g : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C,
        ∃ s : ℕ → K,
          (∀ j : ℕ, W.H a b c d j ≫ g = s j • 𝟙 (𝟙_ C)) ∧
          g = ∑ j ∈ Finset.range (b + c + 1), (s j / ι (h a b c d j)) • W.Hcov a b c d j) ∧
      (∀ f : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d,
        ∃ s : ℕ → K,
          (∀ l : ℕ, f ≫ W.Xcov a b c d l = s l • 𝟙 (𝟙_ C)) ∧
          f = ∑ l ∈ Finset.range (a + b + 1), (s l / ι (x a b c d l)) • W.X a b c d l) ∧
      (∀ g : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C,
        ∃ s : ℕ → K,
          (∀ l : ℕ, W.X a b c d l ≫ g = s l • 𝟙 (𝟙_ C)) ∧
          g = ∑ l ∈ Finset.range (a + b + 1), (s l / ι (x a b c d l)) • W.Xcov a b c d l) ∧
      (∀ j l : ℕ, W.X a b c d l ≫ W.Hcov a b c d j = W.tet a b c d j l) ∧
      (∀ l : ℕ, ∃ s : ℕ → K,
        (∀ j : ℕ, W.tet a b c d j l = s j • 𝟙 (𝟙_ C)) ∧
        W.X a b c d l = ∑ j ∈ Finset.range (b + c + 1),
          (s j / ι (h a b c d j)) • W.H a b c d j) := by
  intro a b c d
  obtain ⟨hH, hX, hHs, hHc, hXs, hXc⟩ := basis_six S W hS hW a b c d
  have ht := basis_overlap S W hS hW a b c d
  refine ⟨hH, hX, hHs, hHc, hXs, hXc, ht, ?_⟩
  intro l
  obtain ⟨s, hs, he⟩ := hHs (W.X a b c d l)
  exact ⟨s, fun j => (ht j l).symm.trans (hs j), he⟩
