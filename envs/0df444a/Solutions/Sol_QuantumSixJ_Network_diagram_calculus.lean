-- Prove2me | solution 1 for QuantumSixJ.Network.diagram_calculus
-- status  : ACCEPTED   (prove)
-- author  : @igor.kh
-- created : 2026-11-13T09:23:42.30068+00:00
-- url     : https://prove2.me/submissions/0bcc4fff-9df1-4c77-9785-4d06d7d861c6

import Definitions.Def_QuantumSixJNetwork
import Theorems.Thm_QuantumSixJ_scalar_foundations

open CategoryTheory MonoidalCategory
universe v u
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


end QuantumSixJ.Network
open QuantumSixJ.Network

theorem solution {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W) :
    (∀ a b c : ℕ,
      W.split c a b ≫ W.fuse a b c =
        (ι (θ a b c) / ι (Δ c)) • 𝟙 (S.V c)) ∧
    (∀ a b c : ℕ, ¬ Admissible (a : ℤ) b c → W.vertex a b c = 0) ∧
    (∀ (a b c : ℕ) (f : S.V a ⊗ S.V b ⊗ S.V c ⟶ 𝟙_ C),
      ∃ t : K, f = t • W.vertex a b c) ∧
    (∀ a b : ℕ,
      (∑ c ∈ fusionRange a b,
        (ι (Δ c) / ι (θ a b c)) • (W.fuse a b c ≫ W.split c a b)) =
          𝟙 (S.V a ⊗ S.V b)) := by
  have hcup := complete_cup_split S W hW
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c
    exact complete_bubble S W hS hW hcup a b c
  · intro a b c hbad
    apply complete_H_vertex_zero S W hS a c b (complete_fuse_cap S W a b c)
    intro hmem
    have hadm := (Finset.mem_filter.mp hmem).2
    apply hbad
    exact (complete_H_admissible_swap (a : ℤ) c b).mp hadm
  · intro a b c f
    apply complete_H_triple_covector S W a b c
      (fun k => ι (θ a b k) / ι (Δ k))
      (complete_resolution S W hS hW hcup a b)
      (complete_fuse_cap S W a b c) f
    · intro k hk z
      exact complete_pair_covector_ne S hS k c hk z
    · exact complete_pair_covector_eq S hS c
  · intro a b
    simpa only [inv_div] using complete_resolution S W hS hW hcup a b
