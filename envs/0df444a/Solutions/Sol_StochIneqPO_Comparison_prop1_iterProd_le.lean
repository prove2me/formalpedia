-- Prove2me | solution 1 for StochIneqPO.Comparison.prop1_iterProd_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:40:59.844308+00:00
-- url     : https://prove2.me/submissions/a4c0d0d1-9252-4158-b953-71c6ac957dc8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_Comparison_iterProd
import Theorems.Thm_StochIneqPO_Comparison_theorem1_tfae

open MeasureTheory ProbabilityTheory Finset StochIneqPO.Comparison

section aux
variable {E : ℕ → Type*} [∀ n, MeasurableSpace (E n)]

set_option backward.isDefEq.respectTransparency false in
lemma iterProd_succ_eq (P₁ : Measure (E 0)) [IsProbabilityMeasure P₁]
    (p : (n : ℕ) → Kernel (Π i : Iic n, E i) (E (n + 1))) [∀ n, IsMarkovKernel (p n)] (m : ℕ) :
    iterProd P₁ p (m + 1) = ((iterProd P₁ p m) ⊗ₘ p m).map
      (fun xz => IicProdIoc m (m + 1) (xz.1, MeasurableEquiv.piSingleton m xz.2)) := by
  have hpart : Kernel.partialTraj p 0 (m + 1) =
      Kernel.partialTraj p m (m + 1) ∘ₖ Kernel.partialTraj p 0 m :=
    Kernel.partialTraj_succ_eq_comp (Nat.zero_le m)
  have : IsProbabilityMeasure (iterProd P₁ p m) := by
    have : IsProbabilityMeasure (P₁.map (MeasurableEquiv.piUnique (fun i : Iic 0 => E i)).symm) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    unfold iterProd; infer_instance
  rw [iterProd, hpart, ← Measure.comp_assoc]
  change Kernel.partialTraj p m (m + 1) ∘ₘ iterProd P₁ p m = _
  rw [Kernel.partialTraj_succ_self, ← Measure.map_comp _ _ (by fun_prop),
    ← Measure.compProd_eq_comp_prod, Measure.compProd_map (MeasurableEquiv.piSingleton m).measurable,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma iterProd_isProb (P₁ : Measure (E 0)) [IsProbabilityMeasure P₁]
    (p : (n : ℕ) → Kernel (Π i : Iic n, E i) (E (n + 1))) [∀ n, IsMarkovKernel (p n)] (m : ℕ) :
    IsProbabilityMeasure (iterProd P₁ p m) := by
  have : IsProbabilityMeasure (P₁.map (MeasurableEquiv.piUnique (fun i : Iic 0 => E i)).symm) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold iterProd; infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma iterProd_zero_eq (P₁ : Measure (E 0))
    (p : (n : ℕ) → Kernel (Π i : Iic n, E i) (E (n + 1))) :
    iterProd P₁ p 0 = P₁.map (MeasurableEquiv.piUnique (fun i : Iic 0 => E i)).symm := by
  rw [iterProd, Kernel.partialTraj_self, Measure.id_comp]

set_option backward.isDefEq.respectTransparency false in
lemma iterProd_zero_integral (P₁ : Measure (E 0))
    (p : (n : ℕ) → Kernel (Π i : Iic n, E i) (E (n + 1))) (f : (Π i : Iic 0, E i) → ℝ)
    (hf : Measurable f) :
    ∫ x, f x ∂(iterProd P₁ p 0) =
      ∫ z, f ((MeasurableEquiv.piUnique (fun i : Iic 0 => E i)).symm z) ∂P₁ := by
  rw [iterProd_zero_eq, integral_map (MeasurableEquiv.measurable _).aemeasurable
    hf.aestronglyMeasurable]
  rfl

lemma ext_mono [∀ n, Preorder (E n)] (m : ℕ) (x x' : Π i : Iic m, E i) (z z' : E (m + 1))
    (hx : x ≤ x') (hz : z ≤ z') :
    IicProdIoc m (m + 1) (x, MeasurableEquiv.piSingleton m z) ≤
      IicProdIoc m (m + 1) (x', MeasurableEquiv.piSingleton m z') := by
  intro i
  simp only [IicProdIoc]
  split_ifs with h
  · exact hx _
  · obtain ⟨j, hj⟩ := i
    have hj' : j = m + 1 := by
      simp only [Finset.mem_Iic] at hj
      simp only at h
      omega
    subst hj'
    exact hz

lemma piUnique_symm_mono [∀ n, Preorder (E n)] (z z' : E 0) (hz : z ≤ z') :
    (MeasurableEquiv.piUnique (fun i : Iic 0 => E i)).symm z ≤
      (MeasurableEquiv.piUnique (fun i : Iic 0 => E i)).symm z' := by
  intro i
  obtain ⟨j, hj⟩ := i
  have hj' : j = 0 := by simpa using hj
  subst hj'
  exact hz

end aux

theorem solution {E : ℕ → Type*} [∀ n, TopologicalSpace (E n)] [∀ n, PolishSpace (E n)]
    [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)] [∀ n, PartialOrder (E n)]
    [∀ n, OrderClosedTopology (E n)]
    (P₁ Q₁ : Measure (E 0)) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    (p q : (n : ℕ) → Kernel (Π i : Iic n, E i) (E (n + 1)))
    [∀ n, IsMarkovKernel (p n)] [∀ n, IsMarkovKernel (q n)]
    (m : ℕ) (hPQ : StochLE P₁ Q₁)
    (hpq : ∀ n < m, ∀ x y : Π i : Iic n, E i, x ≤ y → StochLE (p n x) (q n y)) :
    StochLE (iterProd P₁ p m) (iterProd Q₁ q m) := by
  have hint : ∀ {α : Type _} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
      (g : α → ℝ) (C : ℝ), Measurable g → (∀ x, |g x| ≤ C) → Integrable g μ :=
    fun μ _ g C hg hC => Integrable.of_bound hg.aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)
  induction m with
  | zero =>
    intro f hf hmono hbdd
    obtain ⟨C, hC⟩ := hbdd
    rw [iterProd_zero_integral _ _ f hf, iterProd_zero_integral _ _ f hf]
    exact hPQ _ (hf.comp (MeasurableEquiv.measurable _)) (fun z z' hz => hmono (piUnique_symm_mono z z' hz))
      ⟨C, fun z => hC _⟩
  | succ m ih =>
    have ih' := ih (fun n hn => hpq n (by omega))
    have := iterProd_isProb P₁ p m
    have := iterProd_isProb Q₁ q m
    intro f hf hmono hbdd
    obtain ⟨C, hC⟩ := hbdd
    set ext : (Π i : Iic m, E i) × E (m + 1) → Π i : Iic (m + 1), E i :=
      fun xz => IicProdIoc m (m + 1) (xz.1, MeasurableEquiv.piSingleton m xz.2) with hext
    have hextm : Measurable ext :=
      measurable_IicProdIoc.comp (measurable_fst.prodMk
        ((MeasurableEquiv.piSingleton m).measurable.comp measurable_snd))
    have hfe : Measurable (fun xz => f (ext xz)) := hf.comp hextm
    rw [iterProd_succ_eq, iterProd_succ_eq,
      integral_map hextm.aemeasurable hf.aestronglyMeasurable,
      integral_map hextm.aemeasurable hf.aestronglyMeasurable,
      Measure.integral_compProd (hint _ _ C hfe (fun _ => hC _)),
      Measure.integral_compProd (hint _ _ C hfe (fun _ => hC _))]
    set gp : (Π i : Iic m, E i) → ℝ := fun x => ∫ z, f (ext (x, z)) ∂(p m x) with hgp
    set gq : (Π i : Iic m, E i) → ℝ := fun x => ∫ z, f (ext (x, z)) ∂(q m x) with hgq
    have gpm : Measurable gp := hfe.stronglyMeasurable.integral_kernel_prod_right'.measurable
    have gqm : Measurable gq := hfe.stronglyMeasurable.integral_kernel_prod_right'.measurable
    have hbd : ∀ (ν : Measure (E (m + 1))) [IsProbabilityMeasure ν] (x : Π i : Iic m, E i),
        |∫ z, f (ext (x, z)) ∂ν| ≤ C := by
      intro ν _ x
      have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun z => f (ext (x, z))) (C := C)
        (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hC _)
      simpa [Real.norm_eq_abs] using this
    have hsec : ∀ x : Π i : Iic m, E i, Measurable (fun z : E (m + 1) => f (ext (x, z))) :=
      fun x => hfe.comp measurable_prodMk_left
    have key : ∀ x x' : Π i : Iic m, E i, x ≤ x' → gp x ≤ gq x' := by
      intro x x' h
      calc gp x ≤ ∫ z, f (ext (x', z)) ∂(p m x) :=
            integral_mono (hint _ _ C (hsec x) (fun _ => hC _))
              (hint _ _ C (hsec x') (fun _ => hC _))
              (fun z => hmono (ext_mono m x x' z z h le_rfl))
        _ ≤ gq x' := hpq m (by omega) x x' h _ (hsec x')
              (fun z z' hz => hmono (ext_mono m x' x' z z' le_rfl hz)) ⟨C, fun z => hC _⟩
    obtain ⟨lam, hlam, hsupp, h1, h2⟩ :=
      ((theorem1_tfae (iterProd P₁ p m) (iterProd Q₁ q m)).out 0 1).mp ih'
    change ∫ x, gp x ∂(iterProd P₁ p m) ≤ ∫ x, gq x ∂(iterProd Q₁ q m)
    rw [← h1, ← h2, integral_map measurable_fst.aemeasurable gpm.aestronglyMeasurable,
      integral_map measurable_snd.aemeasurable gqm.aestronglyMeasurable]
    apply integral_mono_ae (hint _ _ C (gpm.comp measurable_fst) (fun _ => hbd _ _))
      (hint _ _ C (gqm.comp measurable_snd) (fun _ => hbd _ _))
    have hae : ∀ᵐ z ∂lam, z.1 ≤ z.2 := by
      rw [ae_iff]
      exact hsupp
    filter_upwards [hae] with z hz
    exact key _ _ hz
