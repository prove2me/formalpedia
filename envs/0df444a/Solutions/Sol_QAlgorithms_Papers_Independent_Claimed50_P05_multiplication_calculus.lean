-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.multiplication_calculus
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:20:34.857051+00:00
-- url     : https://prove2.me/submissions/156159de-7c77-4669-a7f6-60df57852fed

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

namespace X7MC

variable {k : Type*} [RCLike k]
variable {X : Type*} [MeasurableSpace X]

theorem X7_value_bg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
    (T : H →L[k] H) (x : H) : value (boundedGraph T) x = T x := by
  have h : ∃ y, (x, y) ∈ boundedGraph T := ⟨T x, rfl⟩
  unfold value
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem X7_memLp (mu : Measure X) (f : X → k) (hf : Measurable f) (c : ℝ)
    (hc : ∀ x, ‖f x‖ ≤ c) (u : Lp k 2 mu) : MemLp (fun x => f x * u x) 2 mu :=
  MemLp.of_le_mul (Lp.memLp u) (hf.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
    (ae_of_all _ fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _))

def X7_lin (mu : Measure X) (f : X → k) (hf : Measurable f) (c : ℝ)
    (hc : ∀ x, ‖f x‖ ≤ c) : Lp k 2 mu →ₗ[k] Lp k 2 mu where
  toFun u := (X7_memLp mu f hf c hc u).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(X7_memLp mu f hf c hc (u + v)).coeFn_toLp, (X7_memLp mu f hf c hc u).coeFn_toLp,
      (X7_memLp mu f hf c hc v).coeFn_toLp, Lp.coeFn_add u v,
      Lp.coeFn_add ((X7_memLp mu f hf c hc u).toLp _) ((X7_memLp mu f hf c hc v).toLp _)]
      with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply]
    ring
  map_smul' a u := by
    apply Lp.ext
    filter_upwards [(X7_memLp mu f hf c hc (a • u)).coeFn_toLp, (X7_memLp mu f hf c hc u).coeFn_toLp,
      Lp.coeFn_smul a u, Lp.coeFn_smul a ((X7_memLp mu f hf c hc u).toLp _)]
      with x h1 h2 h3 h4
    rw [RingHom.id_apply, h4, h1, h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h2]
    ring

def X7_T (mu : Measure X) (f : X → k) (hf : Measurable f) (c : ℝ)
    (hc : ∀ x, ‖f x‖ ≤ c) : Lp k 2 mu →L[k] Lp k 2 mu :=
  (X7_lin mu f hf c hc).mkContinuous c (fun u => by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(X7_memLp mu f hf c hc u).coeFn_toLp] with x h1
    change ‖((X7_memLp mu f hf c hc u).toLp _ : X → k) x‖ ≤ c * ‖u x‖
    rw [h1, norm_mul]
    exact mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _))

theorem X7_T_ae (mu : Measure X) (f : X → k) (hf : Measurable f) (c : ℝ)
    (hc : ∀ x, ‖f x‖ ≤ c) (u : Lp k 2 mu) :
    (X7_T mu f hf c hc u : X → k) =ᵐ[mu] fun x => f x * u x :=
  (X7_memLp mu f hf c hc u).coeFn_toLp

theorem X7_graph_eq (mu : Measure X) (f : Symbol X k) (c : ℝ)
    (hc : ∀ x, ‖f.val x‖ ≤ c) :
    multiplication mu f = boundedGraph (X7_T mu f.val f.property c hc) := by
  ext p
  simp only [multiplication, boundedGraph, Set.mem_ofPred_eq]
  constructor
  · intro h
    apply Lp.ext
    filter_upwards [h, X7_T_ae mu f.val f.property c hc p.1] with x h1 h2
    rw [h1, h2]
  · intro h
    rw [h]
    exact X7_T_ae mu f.val f.property c hc p.1

theorem X7_inner_T (mu : Measure X) (f : X → k) (hf : Measurable f) (c : ℝ)
    (hc : ∀ x, ‖f x‖ ≤ c) (hf' : Measurable fun x => star (f x))
    (hc' : ∀ x, ‖star (f x)‖ ≤ c) (u w : Lp k 2 mu) :
    inner k (X7_T mu f hf c hc u) w = inner k u (X7_T mu (fun x => star (f x)) hf' c hc' w) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [X7_T_ae mu f hf c hc u, X7_T_ae mu _ hf' c hc' w] with x h1 h2
  simp only [h1, h2, RCLike.inner_apply, starRingEnd_apply, star_mul']
  ring

theorem X7_closed (mu : Measure X) (f : Symbol X k) :
    IsClosed (multiplication mu f) := by
  apply IsSeqClosed.isClosed
  intro p q hp hq
  have h1 : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hq
  have h2 : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hq
  obtain ⟨ns, hns, hns2⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hms2⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (h2.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂mu, ∀ n, (p n).2 x = f.val x * (p n).1 x := ae_all_iff.mpr hp
  change ∀ᵐ x ∂mu, q.2 x = f.val x * q.1 x
  filter_upwards [hns2, hms2, hall] with x hx1 hx2 hx3
  have hA : Tendsto (fun i => (p (ns (ms i))).2 x) atTop (𝓝 (q.2 x)) := hx2
  have hB : Tendsto (fun i => (p (ns (ms i))).2 x) atTop (𝓝 (f.val x * q.1 x)) := by
    simp only [hx3]
    exact ((hx1.comp hms.tendsto_atTop).const_mul (f.val x))
  exact tendsto_nhds_unique hA hB

theorem X7_closedOp (mu : Measure X) (f : Symbol X k) :
    ClosedOperator (k := k) (multiplication mu f) := by
  refine ⟨inferInstance, X7_closed mu f, ?_, ?_, ?_, ?_⟩
  · change ∀ᵐ x ∂mu, (0 : Lp k 2 mu) x = f.val x * (0 : Lp k 2 mu) x
    filter_upwards [Lp.coeFn_zero k 2 mu] with x h
    rw [h]; simp
  · intro x y x2 y2 h h2
    change ∀ᵐ a ∂mu, (y + y2) a = f.val a * (x + x2) a
    filter_upwards [h, h2, Lp.coeFn_add y y2, Lp.coeFn_add x x2] with a ha hb hc hd
    rw [hc, hd]; simp only [Pi.add_apply, ha, hb]; ring
  · intro c x y h
    change ∀ᵐ a ∂mu, (c • y) a = f.val a * (c • x) a
    filter_upwards [h, Lp.coeFn_smul c y, Lp.coeFn_smul c x] with a ha hb hc
    rw [hb, hc]; simp only [Pi.smul_apply, smul_eq_mul, ha]; ring
  · intro x y z h h2
    apply Lp.ext
    filter_upwards [h, h2] with a ha hb
    rw [ha, hb]

theorem X7_proto (mu : Measure X) : ProtoCalculus (multiplication (k := k) mu) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext p
    simp only [multiplication, identity, Set.mem_ofPred_eq, constant, one_mul]
    constructor
    · intro h; exact Lp.ext h
    · intro h; rw [h]; exact ae_of_all _ fun _ => rfl
  · rintro f g p ⟨a, b, ha, hb, hp⟩
    change ∀ᵐ x ∂mu, p.2 x = (f.val x + g.val x) * p.1 x
    rw [hp]
    filter_upwards [ha, hb, Lp.coeFn_add a b] with x h1 h2 h3
    rw [h3]; simp only [Pi.add_apply, h1, h2]; ring
  · rintro c f p ⟨y, hy, hp⟩
    change ∀ᵐ x ∂mu, p.2 x = (c * f.val x) * p.1 x
    rw [hp]
    filter_upwards [hy, Lp.coeFn_smul c y] with x h1 h2
    rw [h2]; simp only [Pi.smul_apply, smul_eq_mul, h1]; ring
  · rintro f g p ⟨z, hz, hp⟩
    change ∀ᵐ x ∂mu, p.2 x = (f.val x * g.val x) * p.1 x
    filter_upwards [hz, hp] with x h1 h2
    rw [h2, h1]; ring
  · intro f g
    ext u
    simp only [graphDomain, mul, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, z, hz, hw⟩
      refine ⟨⟨z, hz⟩, ⟨w, ?_⟩⟩
      change ∀ᵐ x ∂mu, w x = (f.val x * g.val x) * u x
      filter_upwards [hz, hw] with x h1 h2
      change w x = f.val x * z x at h2
      rw [h2, h1]; ring
    · rintro ⟨⟨z, hz⟩, ⟨w, hw⟩⟩
      refine ⟨w, z, hz, ?_⟩
      change ∀ᵐ x ∂mu, w x = f.val x * z x
      change ∀ᵐ x ∂mu, w x = (f.val x * g.val x) * u x at hw
      change ∀ᵐ x ∂mu, z x = g.val x * u x at hz
      filter_upwards [hz, hw] with x h1 h2
      rw [h2, h1]; ring

theorem X7_bounded (mu : Measure X) (f : Symbol X k) (hf : BoundedSymbol f) :
    BoundedOperator (k := k) (multiplication mu f) ∧
      graphAdjoint (k := k) (multiplication mu f) = multiplication mu (starSymbol f) := by
  obtain ⟨c, hc⟩ := hf
  have hc' : ∀ x, ‖(starSymbol f).val x‖ ≤ c := fun x => by
    change ‖star (f.val x)‖ ≤ c
    rw [norm_star]; exact hc x
  refine ⟨⟨_, X7_graph_eq mu f c hc⟩, ?_⟩
  rw [X7_graph_eq mu (starSymbol f) c hc', X7_graph_eq mu f c hc]
  ext p
  simp only [graphAdjoint, boundedGraph, Set.mem_ofPred_eq]
  constructor
  · intro h
    apply ext_inner_left k
    intro x
    rw [h x _ rfl]
    exact X7_inner_T mu f.val f.property c hc (starSymbol f).property hc' x p.1
  · intro h x y hxy
    rw [hxy, h]
    exact (X7_inner_T mu f.val f.property c hc (starSymbol f).property hc' x p.1).symm

theorem X7_weak (mu : Measure X) (fn : ℕ → Symbol X k) (f : Symbol X k) (h : BP fn f) :
    Weak (k := k) (fun n => multiplication mu (fn n)) (multiplication mu f) := by
  obtain ⟨hpt, c, hc⟩ := h
  have hcf : ∀ x, ‖f.val x‖ ≤ c := fun x =>
    le_of_tendsto' ((continuous_norm.tendsto _).comp (hpt x)) (fun n => hc n x)
  refine ⟨fun n => ⟨_, X7_graph_eq mu (fn n) c (hc n)⟩, ⟨_, X7_graph_eq mu f c hcf⟩, ?_⟩
  intro x y
  simp only [X7_graph_eq mu (fn _) c (hc _), X7_graph_eq mu f c hcf, X7_value_bg, L2.inner_def]
  have hcongr : ∀ (g : X → k) (hg : Measurable g) (hgc : ∀ x, ‖g x‖ ≤ c),
      ∫ a, inner k (x a) ((X7_T mu g hg c hgc y) a) ∂mu =
        ∫ a, g a * inner k (x a) (y a) ∂mu := by
    intro g hg hgc
    apply integral_congr_ae
    filter_upwards [X7_T_ae mu g hg c hgc y] with a ha
    rw [ha, ← smul_eq_mul (a := g a) (b := y a), inner_smul_right]
  simp only [hcongr]
  apply tendsto_integral_of_dominated_convergence (fun a => c * ‖inner k (x a) (y a)‖)
  · intro n
    exact ((fn n).property.aestronglyMeasurable).mul (L2.integrable_inner x y).1
  · exact (L2.integrable_inner x y).norm.const_mul c
  · intro n
    filter_upwards with a
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc n a) (norm_nonneg _)
  · filter_upwards with a
    exact (hpt a).mul_const _

end X7MC

end QAlgorithms.Papers.Independent.Claimed50.P05

end

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

open QAlgorithms.Papers.Independent.Claimed50.P05 QAlgorithms.Papers.Independent.Claimed50.P05.X7MC in
theorem solution {k : Type*} [RCLike k] {X : Type*} [MeasurableSpace X] (mu : Measure X) :
    Calculus (multiplication (k := k) mu) :=
  ⟨fun f => X7_closedOp mu f, X7_proto mu, fun f hf => X7_bounded mu f hf,
    fun fn f h => X7_weak mu fn f h⟩

end
