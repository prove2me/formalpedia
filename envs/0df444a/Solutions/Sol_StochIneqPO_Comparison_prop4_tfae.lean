-- Prove2me | solution 1 for StochIneqPO.Comparison.prop4_tfae
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:45:08.799012+00:00
-- url     : https://prove2.me/submissions/e701d489-1292-4b5a-8333-9f48ee89ca8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_Comparison_IsUpward
import Theorems.Thm_StochIneqPO_Comparison_theorem1_tfae

open MeasureTheory ProbabilityTheory Finset StochIneqPO.Comparison

set_option backward.isDefEq.respectTransparency false in
lemma chain_exists_of_upward {E : Type*} [MeasurableSpace E] [Preorder E]
    (hmeas : ∀ a : ℕ, MeasurableSet {z : (Π _ : Iic a, E) × E | z.1 ⟨a, mem_Iic.2 le_rfl⟩ ≤ z.2})
    (P : ℕ → Measure E) [∀ i, IsProbabilityMeasure (P i)]
    (k : ℕ → Kernel E E) [∀ i, IsMarkovKernel (k i)] (hup : ∀ i, IsUpward (k i))
    (hk : ∀ i, P (i + 1) = (P i ⊗ₘ k i).snd) :
    ∃ T : Measure (ℕ → E), IsProbabilityMeasure T ∧ (∀ i, T.map (fun x => x i) = P i) ∧
      ∀ᵐ x ∂T, ∀ i, x i ≤ x (i + 1) := by
  let π : (a : ℕ) → (Π _ : Iic a, E) → E := fun a y => y ⟨a, mem_Iic.2 le_rfl⟩
  have hπ : ∀ a, Measurable (π a) := fun a => measurable_pi_apply _
  let κ : (n : ℕ) → Kernel (Π _ : Iic n, E) E := fun n => (k n).comap (π n) (hπ n)
  have hκ : ∀ n, IsMarkovKernel (κ n) := fun n => by
    simp only [κ]; infer_instance
  let T := Kernel.trajMeasure (X := fun _ => E) (P 0) κ
  have hfr : ∀ a, (fun x : ℕ → E => x a) = π a ∘ Preorder.frestrictLe a := fun a => rfl
  have hstep : ∀ a, T.map (fun x => (Preorder.frestrictLe a x, x (a + 1))) =
      T.map (Preorder.frestrictLe a) ⊗ₘ κ a :=
    fun a => Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm
  refine ⟨T, inferInstance, ?_, ?_⟩
  · intro i
    induction i with
    | zero =>
      rw [hfr 0, ← Measure.map_map (hπ 0) (Preorder.measurable_frestrictLe 0)]
      simp only [T]
      rw [Kernel.trajMeasure, Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
        Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
        Measure.map_map (hπ 0) (MeasurableEquiv.measurable _)]
      have : π 0 ∘ (MeasurableEquiv.piUnique (fun i : Iic 0 => (fun _ => E) i)).symm = id := by
        funext z
        rfl
      rw [this, Measure.map_id]
    | succ a ih =>
      have : (fun x : ℕ → E => x (a + 1)) =
          Prod.snd ∘ (fun x => (Preorder.frestrictLe a x, x (a + 1))) := rfl
      rw [this, ← Measure.map_map measurable_snd (by fun_prop), hstep, ← Measure.snd,
        Measure.snd_compProd, hk, Measure.snd_compProd, ← ih, hfr a,
        ← Measure.map_map (hπ a) (Preorder.measurable_frestrictLe a)]
      ext s hs
      rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
        lintegral_map (Kernel.measurable_coe _ hs) (hπ a)]
      rfl
  · rw [ae_all_iff]
    intro a
    have hS := (hmeas a).compl
    rw [ae_iff]
    have hset : {x : ℕ → E | ¬ x a ≤ x (a + 1)} =
        (fun x => (Preorder.frestrictLe a x, x (a + 1))) ⁻¹'
          {z : (Π _ : Iic a, E) × E | z.1 ⟨a, mem_Iic.2 le_rfl⟩ ≤ z.2}ᶜ := rfl
    rw [hset, ← Measure.map_apply (by fun_prop) hS, hstep, Measure.compProd_apply hS]
    have h0 : ∀ y : Π _ : Iic a, E,
        κ a y (Prod.mk y ⁻¹' {z : (Π _ : Iic a, E) × E | z.1 ⟨a, mem_Iic.2 le_rfl⟩ ≤ z.2}ᶜ) = 0 :=
      fun y => hup a (π a y)
    exact (lintegral_congr h0).trans lintegral_zero

theorem solution {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P : ℕ → Measure E) [∀ i, IsProbabilityMeasure (P i)] :
    List.TFAE
      [ -- (i)
        ∀ i, StochLE (P i) (P (i + 1)),
        -- (ii)
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
          ∃ X : ℕ → Ω → E, (∀ i, Measurable (X i)) ∧ (∀ᵐ ω ∂μ, ∀ i, X i ω ≤ X (i + 1) ω) ∧
            ∀ i, μ.map (X i) = P i,
        -- (iii)
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
          ∃ (Z : Ω → ℝ) (f : ℕ → ℝ → E), Measurable Z ∧ (∀ i, Measurable (f i)) ∧
            (∀ i t, f i t ≤ f (i + 1) t) ∧ ∀ i, μ.map (fun ω => f i (Z ω)) = P i ] := by
  tfae_have 1 → 3 := by
    intro h
    have hv := fun i => ((theorem1_tfae (P i) (P (i + 1))).out 0 4).mp (h i)
    choose k hkM hkU hkP using hv
    have hmeas : ∀ a : ℕ,
        MeasurableSet {z : (Π _ : Iic a, E) × E | z.1 ⟨a, mem_Iic.2 le_rfl⟩ ≤ z.2} :=
      fun a => measurableSet_le ((measurable_pi_apply _).comp measurable_fst) measurable_snd
    obtain ⟨T, hT, hmarg, hmono⟩ := chain_exists_of_upward hmeas P k hkU hkP
    have : Nonempty E := nonempty_of_isProbabilityMeasure (P 0)
    have : Nonempty (ℕ → E) := inferInstance
    obtain ⟨ψ, hψ⟩ := exists_measurableEmbedding_real (α := ℕ → E)
    let G : Set (ℕ → E) := {x | ∀ i, x i ≤ x (i + 1)}
    have hG : MeasurableSet G := by
      have : G = ⋂ i, {x : ℕ → E | x i ≤ x (i + 1)} := by ext x; simp [G]
      rw [this]
      exact MeasurableSet.iInter fun i =>
        measurableSet_le (measurable_pi_apply i) (measurable_pi_apply (i + 1))
    let e0 : E := Classical.arbitrary E
    classical
    let F : ℝ → ℕ → E := fun t => if t ∈ ψ '' G then hψ.invFun t else fun _ => e0
    have hF : Measurable F :=
      Measurable.ite (hψ.measurableSet_image' hG) hψ.measurable_invFun measurable_const
    have hFψ : ∀ x ∈ G, F (ψ x) = x := fun x hx => by
      simp only [F, if_pos (Set.mem_image_of_mem ψ hx)]
      exact hψ.leftInverse_invFun x
    have hTψ : IsProbabilityMeasure (T.map ψ) :=
      Measure.isProbabilityMeasure_map hψ.measurable.aemeasurable
    refine ⟨ℝ, inferInstance, T.map ψ, hTψ, id, fun i t => F t i, measurable_id,
      fun i => (measurable_pi_apply i).comp hF, ?_, ?_⟩
    · intro i t
      by_cases ht : t ∈ ψ '' G
      · obtain ⟨x, hx, rfl⟩ := ht
        simp only [hFψ x hx]
        exact hx i
      · have hF' : F t = fun _ => e0 := by simp only [F, if_neg ht]
        simp only [hF', le_refl]
    · intro i
      rw [show (fun ω => (fun i t => F t i) i (id ω)) = (fun x : ℕ → E => x i) ∘ F from rfl,
        Measure.map_map ((measurable_pi_apply i).comp hF) hψ.measurable, ← hmarg i]
      apply Measure.map_congr
      filter_upwards [hmono] with x hx
      simp [hFψ x hx]
  tfae_have 3 → 2 := by
    rintro ⟨Ω, mΩ, μ, hμ, Z, f, hZ, hf, hmono, hlaw⟩
    exact ⟨Ω, mΩ, μ, hμ, fun i ω => f i (Z ω), fun i => (hf i).comp hZ,
      ae_of_all _ (fun ω i => hmono i (Z ω)), hlaw⟩
  tfae_have 2 → 1 := by
    rintro ⟨Ω, mΩ, μ, hμ, X, hX, hle, hlaw⟩ i g hg hgm ⟨C, hC⟩
    have hint : ∀ j, Integrable (fun ω => g (X j ω)) μ := fun j =>
      Integrable.of_bound (hg.comp (hX j)).aestronglyMeasurable C
        (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC (X j ω))
    rw [← hlaw i, ← hlaw (i + 1), integral_map (hX i).aemeasurable hg.aestronglyMeasurable,
      integral_map (hX (i + 1)).aemeasurable hg.aestronglyMeasurable]
    apply integral_mono_ae (hint i) (hint (i + 1))
    filter_upwards [hle] with ω h
    exact hgm (h i)
  tfae_finish
