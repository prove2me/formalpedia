-- Prove2me | solution 1 for SmoothedSimplex.Shadow.shadow_card_ae_le_edgeCount
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T16:42:01.014282+00:00
-- url     : https://prove2.me/submissions/cb332dc4-bd03-4974-ad54-65e591aaa34f

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_shadow
import Definitions.Def_SmoothedSimplex_Shadow_shadowBound
import Definitions.Def_FriendlyShadow_Gaussian_Model

set_option autoImplicit false



/-! O1c/O1b general position: almost surely (rows with densities)
(G1) any d+1 rows affinely span ℝᵈ, (G2) W together with any d-2 rows spans ℝᵈ. -/

namespace FSGP

open MeasureTheory FriendlyShadow.Gaussian
open scoped ENNReal

theorem meas_bad {d n k : ℕ} (c : (Fin n → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (g : (Fin n → EuclideanSpace ℝ (Fin d)) → Fin k → EuclideanSpace ℝ (Fin d))
    (hc : Continuous c) (hg : Continuous g) (i : Fin n) :
    MeasurableSet {a : Fin n → EuclideanSpace ℝ (Fin d) |
      a i - c a ∈ Submodule.span ℝ (Set.range (g a))} := by
  set C : Set ((Fin k → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) :=
    {p | ∑ j, p.1 j • g p.2 j = p.2 i - c p.2} with hCdef
  have hCc : IsClosed C := isClosed_eq (by fun_prop) (by fun_prop)
  have hC : IsSigmaCompact C := isSigmaCompact_univ.of_isClosed_subset hCc (Set.subset_univ _)
  have himg : {a : Fin n → EuclideanSpace ℝ (Fin d) |
      a i - c a ∈ Submodule.span ℝ (Set.range (g a))} = Prod.snd '' C := by
    ext a
    simp only [Set.mem_ofPred_eq, Submodule.mem_span_range_iff_exists_fun, Set.mem_image]
    constructor
    · rintro ⟨f, hf⟩; exact ⟨(f, a), hf, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨q.1, hq⟩
  obtain ⟨K, hK, hU⟩ := hC.image continuous_snd
  rw [himg, ← hU]
  exact MeasurableSet.iUnion fun m => (hK m).isClosed.measurableSet

theorem dens_null_coset {d k : ℕ} (hk : k < d) (μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (c0 : EuclideanSpace ℝ (Fin d)) (g0 : Fin k → EuclideanSpace ℝ (Fin d)) :
    densityMeasure μ {x | x - c0 ∈ Submodule.span ℝ (Set.range g0)} = 0 := by
  have hS : Submodule.span ℝ (Set.range g0) ≠ ⊤ := by
    intro h
    have h1 := finrank_range_le_card (R := ℝ) g0
    unfold Set.finrank at h1
    rw [h, finrank_top, finrank_euclideanSpace_fin, Fintype.card_fin] at h1
    omega
  have hA : AffineSubspace.mk' c0 (Submodule.span ℝ (Set.range g0)) ≠ ⊤ := by
    intro h
    apply hS
    have := congrArg AffineSubspace.direction h
    rwa [AffineSubspace.direction_mk', AffineSubspace.direction_top] at this
  have hset : {x | x - c0 ∈ Submodule.span ℝ (Set.range g0)} =
      (AffineSubspace.mk' c0 (Submodule.span ℝ (Set.range g0)) : Set (EuclideanSpace ℝ (Fin d))) := by
    ext x
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub]
  have h0 : volume ((AffineSubspace.mk' c0 (Submodule.span ℝ (Set.range g0)) :
      Set (EuclideanSpace ℝ (Fin d)))) = 0 :=
    Measure.addHaar_affineSubspace volume _ hA
  rw [hset]
  unfold densityMeasure
  exact withDensity_absolutelyContinuous _ _ h0

theorem one_row_null {d n k : ℕ} (hk : k < d) (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ)
    (i : Fin (n + 1)) (c : (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (g : (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) → Fin k → EuclideanSpace ℝ (Fin d))
    (hc : Continuous c) (hg : Continuous g)
    (hci : ∀ a x, c (Function.update a i x) = c a)
    (hgi : ∀ a x, g (Function.update a i x) = g a) :
    rowLaw μ {a | a i - c a ∈ Submodule.span ℝ (Set.range (g a))} = 0 := by
  have : ∀ j, SigmaFinite (densityMeasure (μ j)) := fun j => by
    unfold densityMeasure; infer_instance
  set B := {a : Fin (n + 1) → EuclideanSpace ℝ (Fin d) |
    a i - c a ∈ Submodule.span ℝ (Set.range (g a))} with hBdef
  have hB : MeasurableSet B := meas_bad c g hc hg i
  have hmp := MeasurePreserving.symm _
    (measurePreserving_piFinSuccAbove (fun j => densityMeasure (μ j)) i)
  unfold rowLaw
  rw [← hmp.measure_preimage_equiv B]
  set e := (MeasurableEquiv.piFinSuccAbove (fun _ => EuclideanSpace ℝ (Fin d)) i).symm with hedef
  have hB' : MeasurableSet (e ⁻¹' B) := e.measurable hB
  rw [Measure.prod_apply_symm hB']
  have hsec : ∀ y, densityMeasure (μ i) ((fun x => (x, y)) ⁻¹' (e ⁻¹' B)) = 0 := by
    intro y
    have hset : (fun x => (x, y)) ⁻¹' (e ⁻¹' B) =
        {x | x - c (e (0, y)) ∈ Submodule.span ℝ (Set.range (g (e (0, y))))} := by
      ext x
      have h1 : e (x, y) = Function.update (e (0, y)) i x := by
        simp only [hedef, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.update_insertNth]
      simp only [Set.mem_preimage, hBdef, Set.mem_ofPred_eq]
      rw [h1, hci, hgi, Function.update_self]
    rw [hset]
    exact dens_null_coset hk _ _ _
  simp [hsec]

theorem gen_li {d n p : ℕ} (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin d)) (hw : LinearIndependent ℝ w)
    (c : (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) (hc : Continuous c) :
    ∀ (m : ℕ) (s : Fin m → Fin (n + 1)), Function.Injective s → p + m ≤ d →
      (∀ k a x, c (Function.update a (s k) x) = c a) →
      ∀ᵐ a ∂rowLaw μ, LinearIndependent ℝ (Fin.append w (fun k => a (s k) - c a)) := by
  intro m
  induction m with
  | zero =>
    intro s _ _ _
    refine Filter.Eventually.of_forall (fun a => ?_)
    have h0 : (fun k : Fin 0 => a (s k) - c a) = Fin.elim0 := funext (fun k => k.elim0)
    rw [h0, Fin.append_elim0]
    exact hw.comp _ (Fin.cast_injective _)
  | succ m ih =>
    intro s hs hpm hcs
    have h1 := ih (s ∘ Fin.castSucc) (hs.comp (Fin.castSucc_injective m)) (by omega)
      (fun k a x => hcs _ a x)
    set i := s (Fin.last m) with hi
    have hne : ∀ k : Fin m, s k.castSucc ≠ i := fun k h =>
      (Fin.castSucc_lt_last k).ne (hs h)
    have hgc : Continuous (fun a : Fin (n + 1) → EuclideanSpace ℝ (Fin d) =>
        Fin.append w (fun k : Fin m => a (s k.castSucc) - c a)) := by
      refine continuous_pi (fun j => ?_)
      induction j using Fin.addCases with
      | left l => simp only [Fin.append_left]; exact continuous_const
      | right l => simp only [Fin.append_right]; exact (continuous_apply _).sub hc
    have h0 := one_row_null (k := p + m) (by omega) μ i c
      (fun a => Fin.append w (fun k : Fin m => a (s k.castSucc) - c a)) hc hgc
      (fun a x => hcs _ a x) (fun a x => by
        beta_reduce
        rw [hcs (Fin.last m) a x]
        congr 1
        funext k
        rw [Function.update_of_ne (hne k)])
    have h2 := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [h1, h2] with a ha1 ha2
    have hsn : (fun k : Fin (m + 1) => a (s k) - c a) =
        Fin.snoc (fun k : Fin m => a (s k.castSucc) - c a) (a i - c a) := by
      funext k
      induction k using Fin.lastCases with
      | last => simp [hi]
      | cast j => simp
    rw [hsn, Fin.append_snoc, linearIndependent_finSnoc]
    exact ⟨ha1, ha2⟩

/-- (G1) a.s.: for every injective `t : Fin (d+1) → Fin (n+1)` the `d` difference vectors are
linearly independent. -/
theorem g1_ae {d n : ℕ} (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ) :
    ∀ᵐ a ∂rowLaw μ, ∀ t : Fin (d + 1) → Fin (n + 1), Function.Injective t →
      LinearIndependent ℝ (fun k : Fin d => a (t k.succ) - a (t 0)) := by
  rw [ae_all_iff]
  intro t
  by_cases ht : Function.Injective t
  · have h := gen_li μ (Fin.elim0 : Fin 0 → EuclideanSpace ℝ (Fin d))
      (linearIndependent_empty_type) (fun a => a (t 0)) (continuous_apply _) d (t ∘ Fin.succ)
      (ht.comp (Fin.succ_injective _)) (by omega)
      (fun k a x => Function.update_of_ne (fun h => Fin.succ_ne_zero k (ht h).symm) _ _)
    filter_upwards [h] with a ha _
    rw [Fin.elim0_append] at ha
    have := ha.comp (Fin.cast (Nat.zero_add d).symm) (Fin.cast_injective _)
    simpa [Function.comp_def] using this
  · exact Filter.Eventually.of_forall (fun a h => absurd h ht)

/-- (G2) a.s.: a fixed independent pair `w` together with any `d-2` distinct rows is independent. -/
theorem g2_ae {d n : ℕ} (hd : 2 ≤ d) (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ)
    (w : Fin 2 → EuclideanSpace ℝ (Fin d)) (hw : LinearIndependent ℝ w) :
    ∀ᵐ a ∂rowLaw μ, ∀ t : Fin (d - 2) → Fin (n + 1), Function.Injective t →
      LinearIndependent ℝ (Fin.append w (fun k => a (t k))) := by
  rw [ae_all_iff]
  intro t
  by_cases ht : Function.Injective t
  · have h := gen_li μ w hw (fun _ => 0) continuous_const (d - 2) t ht (by omega)
      (fun _ _ _ => rfl)
    filter_upwards [h] with a ha _
    simpa using ha
  · exact Filter.Eventually.of_forall (fun a h => absurd h ht)

end FSGP



/-! O1b/O1c deterministic part: under general position, every edge of `Q ∩ W` is
`conv(a_I) ∩ W` for a unique `I` with `|I| = d`. -/

namespace FSFace

open MeasureTheory FriendlyShadow.Gaussian
open scoped ENNReal

/-- (G1) deterministic form: any `d+1` rows affinely span, with explicit coefficients. -/
def G1det {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ S : Finset (Fin n), d + 1 ≤ S.card → ∀ z : EuclideanSpace ℝ (Fin d),
    ∃ c : Fin n → ℝ, (∀ i, i ∉ S → c i = 0) ∧ ∑ i, c i = 0 ∧ ∑ i, c i • a i = z

/-- (G2) deterministic form: the hull of at most `d-1` rows meets `W` in at most one point. -/
def G2det {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ J : Finset (Fin n), J.card + 1 ≤ d → ∀ x y : EuclideanSpace ℝ (Fin d), x ∈ W → y ∈ W →
    x ∈ convexHull ℝ (a '' ↑J) → y ∈ convexHull ℝ (a '' ↑J) → x = y

theorem hull_rep {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (J : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ convexHull ℝ (a '' ↑J)) :
    ∃ α : Fin n → ℝ, (∀ i, 0 ≤ α i) ∧ (∀ i, i ∉ J → α i = 0) ∧ ∑ i, α i = 1 ∧
      ∑ i, α i • a i = x := by
  classical
  have hsub : convexHull ℝ (a '' ↑J) ⊆ {y | ∃ α : Fin n → ℝ, (∀ i, 0 ≤ α i) ∧
      (∀ i, i ∉ J → α i = 0) ∧ ∑ i, α i = 1 ∧ ∑ i, α i • a i = y} := by
    apply convexHull_min
    · rintro _ ⟨j, hj, rfl⟩
      refine ⟨Pi.single j 1, fun i => ?_, fun i hi => ?_, by simp, by simp [Pi.single_apply]⟩
      · by_cases h : i = j
        · subst h; simp
        · simp [h]
      · have : i ≠ j := fun h => hi (h ▸ hj)
        simp [this]
    · rintro _ ⟨μ, hμ0, hμJ, hμ1, rfl⟩ _ ⟨ν, hν0, hνJ, hν1, rfl⟩ s t hs ht hst
      refine ⟨fun i => s * μ i + t * ν i, fun i => ?_, fun i hi => ?_, ?_, ?_⟩
      · have := hμ0 i; have := hν0 i; positivity
      · simp [hμJ i hi, hνJ i hi]
      · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, hν1, hst]
      · simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  exact hsub hx

theorem hull_of_rep {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (J : Finset (Fin n))
    (α : Fin n → ℝ) (h0 : ∀ i, 0 ≤ α i) (hJ : ∀ i, i ∉ J → α i = 0) (h1 : ∑ i, α i = 1) :
    ∑ i, α i • a i ∈ convexHull ℝ (a '' ↑J) := by
  classical
  have e1 : ∑ i ∈ J, α i = ∑ i, α i :=
    Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => hJ i hi)
  have e2 : ∑ i ∈ J, α i • a i = ∑ i, α i • a i :=
    Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => by simp [hJ i hi])
  rw [← e2]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => h0 i) (e1.trans h1)
    (fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩)

theorem pert_eps {n : ℕ} (wt c : Fin n → ℝ) (h0 : ∀ i, 0 ≤ wt i)
    (hc : ∀ i, c i ≠ 0 → 0 < wt i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 0 ≤ wt i + ε * c i := by
  set Q := ∑ i, |c i| / wt i with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => div_nonneg (abs_nonneg _) (h0 i))
  refine ⟨1 / (1 + Q), by positivity, fun i => ?_⟩
  by_cases hci : c i = 0
  · simp [hci, h0 i]
  · have hw := hc i hci
    have hle : |c i| / wt i ≤ Q :=
      Finset.single_le_sum (f := fun i => |c i| / wt i)
        (fun j _ => div_nonneg (abs_nonneg _) (h0 j)) (Finset.mem_univ i)
    have h2 : |c i| ≤ Q * wt i := (div_le_iff₀ hw).1 hle
    have h3 := neg_abs_le (c i)
    have heq : wt i + 1 / (1 + Q) * c i = (wt i * (1 + Q) + c i) / (1 + Q) := by
      field_simp
    rw [heq]
    apply div_nonneg _ (by positivity)
    nlinarith

theorem pert_mem {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (wt c : Fin n → ℝ) (h0 : ∀ i, 0 ≤ wt i)
    (h1 : ∑ i, wt i = 1) (hc0 : ∑ i, c i = 0) (hc : ∀ i, c i ≠ 0 → 0 < wt i)
    (hmW : ∑ i, wt i • a i ∈ W) (hzW : ∑ i, c i • a i ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ ∑ i, wt i • a i + ε • ∑ i, c i • a i ∈ polygon W a := by
  obtain ⟨ε, hε, hεi⟩ := pert_eps wt c h0 hc
  refine ⟨ε, hε, ?_⟩
  show _ ∈ convexHull ℝ (Set.range a) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))
  refine ⟨?_, W.add_mem hmW (W.smul_mem _ hzW)⟩
  have heq : ∑ i, wt i • a i + ε • ∑ i, c i • a i = ∑ i, (wt i + ε * c i) • a i := by
    simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  rw [heq]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => hεi i) ?_
    (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, h1, hc0]

theorem mid_mem_W {d n : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {u v : EuclideanSpace ℝ (Fin d)}
    (huv : Hirsch.Adj (polygon W a) u v) : midpoint ℝ u v ∈ W := by
  have hu : u ∈ polygon W a := huv.2.1 (left_mem_segment ℝ u v)
  have hv : v ∈ polygon W a := huv.2.1 (right_mem_segment ℝ u v)
  rw [midpoint_eq_smul_add]
  exact W.smul_mem _ (W.add_mem hu.2 hv.2)

theorem mid_mem_seg {d' : ℕ} (u v : EuclideanSpace ℝ (Fin d')) : midpoint ℝ u v ∈ segment ℝ u v := by
  rw [segment_eq_image_lineMap]
  exact ⟨1/2, by norm_num, by
    rw [midpoint, AffineMap.lineMap_apply, AffineMap.lineMap_apply]; norm_num [invOf_eq_inv]⟩

/-- Key lemma (K): a positive convex representation of the midpoint of an edge uses at most `d` rows. -/
theorem key_card {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    {u v : EuclideanSpace ℝ (Fin d)} (huv : Hirsch.Adj (polygon W a) u v) (wt : Fin n → ℝ)
    (h0 : ∀ i, 0 ≤ wt i) (h1 : ∑ i, wt i = 1) (hm : ∑ i, wt i • a i = midpoint ℝ u v) :
    (Finset.univ.filter (fun i => 0 < wt i)).card ≤ d := by
  classical
  by_contra hlt
  push_neg at hlt
  have hmW := mid_mem_W huv
  obtain ⟨z, hzW, hz⟩ : ∃ z ∈ W, z ∉ ℝ ∙ (v - u) := by
    by_contra h
    push_neg at h
    have hle : W ≤ ℝ ∙ (v - u) := fun z hz => h z hz
    have h1' := Submodule.finrank_mono hle
    have h2 := finrank_span_le_card (R := ℝ) ({v - u} : Set (EuclideanSpace ℝ (Fin d)))
    simp at h2
    omega
  obtain ⟨c, hcS, hc0, hcz⟩ := hG1 (Finset.univ.filter (fun i => 0 < wt i)) (by omega) z
  have hc : ∀ i, c i ≠ 0 → 0 < wt i := by
    intro i hci
    by_contra hw
    exact hci (hcS i (by simpa using hw))
  have hc' : ∀ i, (-c) i ≠ 0 → 0 < wt i := fun i h => hc i (by simpa using h)
  obtain ⟨ε₁, hε₁, hp₁⟩ := pert_mem W a wt c h0 h1 hc0 hc (hm ▸ hmW) (hcz ▸ hzW)
  obtain ⟨ε₂, hε₂, hp₂⟩ := pert_mem W a wt (-c) h0 h1 (by simp [hc0]) hc' (hm ▸ hmW)
    (by simpa [neg_smul, Finset.sum_neg_distrib, hcz] using W.neg_mem hzW)
  rw [hm, hcz] at hp₁
  have hneg : ∑ i, (-c) i • a i = -z := by simp [neg_smul, Finset.sum_neg_distrib, hcz]
  rw [hm, hneg] at hp₂
  set m := midpoint ℝ u v with hmdef
  have hopen : m ∈ openSegment ℝ (m + ε₂ • -z) (m + ε₁ • z) := by
    have hs : ε₁ + ε₂ ≠ 0 := by positivity
    have hab : ε₁ / (ε₁ + ε₂) + ε₂ / (ε₁ + ε₂) = 1 := by field_simp
    have hab2 : ε₂ / (ε₁ + ε₂) * ε₁ - ε₁ / (ε₁ + ε₂) * ε₂ = 0 := by ring
    refine ⟨ε₁ / (ε₁ + ε₂), ε₂ / (ε₁ + ε₂), by positivity, by positivity, hab, ?_⟩
    calc (ε₁ / (ε₁ + ε₂)) • (m + ε₂ • -z) + (ε₂ / (ε₁ + ε₂)) • (m + ε₁ • z)
        = (ε₁ / (ε₁ + ε₂) + ε₂ / (ε₁ + ε₂)) • m +
          (ε₂ / (ε₁ + ε₂) * ε₁ - ε₁ / (ε₁ + ε₂) * ε₂) • z := by module
      _ = m := by rw [hab, hab2, zero_smul, one_smul, add_zero]
  have hseg := huv.2.right_mem_of_mem_openSegment hp₂ hp₁ (mid_mem_seg u v) hopen
  rw [segment_eq_image'] at hseg
  obtain ⟨θ, _, hθ⟩ := hseg
  apply hz
  have hez : ε₁ • z = (θ - 1 / 2) • (v - u) := by
    have : m = u + (1 / 2 : ℝ) • (v - u) := by
      rw [hmdef, midpoint_eq_smul_add]; simp only [invOf_eq_inv]; module
    rw [this] at hθ
    have := congrArg (fun x => x - (u + (1 / 2 : ℝ) • (v - u))) hθ
    simp only [add_sub_cancel_left] at this
    rw [← this]; module
  have : z = ε₁⁻¹ • ((θ - 1 / 2) • (v - u)) := by
    rw [← hez, smul_smul, inv_mul_cancel₀ hε₁.ne', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem core_seg {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) {u v : EuclideanSpace ℝ (Fin d)}
    (huv : Hirsch.Adj (polygon W a) u v) (wt : Fin n → ℝ)
    (h0 : ∀ i, 0 ≤ wt i) (h1 : ∑ i, wt i = 1) (hm : ∑ i, wt i • a i = midpoint ℝ u v)
    (y : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ convexHull ℝ (a '' ↑(Finset.univ.filter (fun i => 0 < wt i)))) (hyW : y ∈ W) :
    y ∈ segment ℝ u v := by
  classical
  obtain ⟨γ, hγ0, hγS, hγ1, hγy⟩ := hull_rep a _ y hy
  have hc : ∀ i, (wt - γ) i ≠ 0 → 0 < wt i := by
    intro i hi
    by_contra hw
    have hw0 : wt i = 0 := le_antisymm (not_lt.1 hw) (h0 i)
    have : γ i = 0 := hγS i (by simp [hw])
    exact hi (by simp [hw0, this])
  have hzsum : ∑ i, (wt - γ) i • a i = midpoint ℝ u v - y := by
    simp [sub_smul, Finset.sum_sub_distrib, hm, hγy]
  have hmW := mid_mem_W huv
  obtain ⟨ε, hε, hp⟩ := pert_mem W a wt (wt - γ) h0 h1
    (by simp [Finset.sum_sub_distrib, h1, hγ1]) hc (hm ▸ hmW)
    (hzsum ▸ W.sub_mem hmW hyW)
  rw [hm, hzsum] at hp
  have hyP : y ∈ polygon W a := by
    show y ∈ convexHull ℝ (Set.range a) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))
    exact ⟨convexHull_mono (Set.image_subset_range _ _) hy, hyW⟩
  have hopen : midpoint ℝ u v ∈
      openSegment ℝ (midpoint ℝ u v + ε • (midpoint ℝ u v - y)) y := by
    have hs : 1 + ε ≠ 0 := by positivity
    have hab : 1 / (1 + ε) + ε / (1 + ε) = 1 := by field_simp
    have hab1 : 1 / (1 + ε) * (1 + ε) = 1 := by field_simp
    have hab2 : ε / (1 + ε) - 1 / (1 + ε) * ε = 0 := by ring
    refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, hab, ?_⟩
    calc (1 / (1 + ε)) • (midpoint ℝ u v + ε • (midpoint ℝ u v - y)) + (ε / (1 + ε)) • y
        = (1 / (1 + ε) * (1 + ε)) • midpoint ℝ u v + (ε / (1 + ε) - 1 / (1 + ε) * ε) • y := by
          module
      _ = midpoint ℝ u v := by rw [hab1, hab2, zero_smul, one_smul, add_zero]
  exact huv.2.right_mem_of_mem_openSegment hp hyP (mid_mem_seg u v) hopen

theorem mid_rep {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (u v : EuclideanSpace ℝ (Fin d))
    (α β : Fin n → ℝ) (hαu : ∑ i, α i • a i = u) (hβv : ∑ i, β i • a i = v) :
    ∑ i, ((α i + β i) / 2) • a i = midpoint ℝ u v := by
  have : ∑ i, ((α i + β i) / 2) • a i = (1 / 2 : ℝ) • (∑ i, α i • a i + ∑ i, β i • a i) := by
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    module
  rw [this, hαu, hβv, midpoint_eq_smul_add]
  simp only [invOf_eq_inv]
  module

theorem face_exists {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) {u v : EuclideanSpace ℝ (Fin d)} (huv : Hirsch.Adj (polygon W a) u v) :
    ∃ I : Finset (Fin n), I.card = d ∧
      convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v := by
  classical
  have hu : u ∈ polygon W a := huv.2.1 (left_mem_segment ℝ u v)
  have hv : v ∈ polygon W a := huv.2.1 (right_mem_segment ℝ u v)
  have hrange : convexHull ℝ (Set.range a) = convexHull ℝ (a '' ↑(Finset.univ : Finset (Fin n))) := by
    rw [Finset.coe_univ, Set.image_univ]
  obtain ⟨α, hα0, -, hα1, hαu⟩ := hull_rep a Finset.univ u (hrange ▸ hu.1)
  obtain ⟨β, hβ0, -, hβ1, hβv⟩ := hull_rep a Finset.univ v (hrange ▸ hv.1)
  set wt : Fin n → ℝ := fun i => (α i + β i) / 2 with hwt
  have h0 : ∀ i, 0 ≤ wt i := fun i => by have := hα0 i; have := hβ0 i; positivity
  have h1 : ∑ i, wt i = 1 := by
    simp only [hwt, ← Finset.sum_div, Finset.sum_add_distrib, hα1, hβ1]; norm_num
  have hm : ∑ i, wt i • a i = midpoint ℝ u v := mid_rep a u v α β hαu hβv
  set S := Finset.univ.filter (fun i => 0 < wt i) with hS
  have hcard := key_card W hW a hG1 huv wt h0 h1 hm
  have hαS : ∀ i, i ∉ S → α i = 0 := by
    intro i hi
    have : ¬ 0 < wt i := by simpa [hS] using hi
    have := hα0 i; have := hβ0 i
    simp only [hwt] at *
    linarith [not_lt.1 ‹¬ 0 < (α i + β i) / 2›]
  have hβS : ∀ i, i ∉ S → β i = 0 := by
    intro i hi
    have : ¬ 0 < wt i := by simpa [hS] using hi
    have := hα0 i; have := hβ0 i
    simp only [hwt] at *
    linarith [not_lt.1 ‹¬ 0 < (α i + β i) / 2›]
  have huS : u ∈ convexHull ℝ (a '' ↑S) := hαu ▸ hull_of_rep a S α hα0 hαS hα1
  have hvS : v ∈ convexHull ℝ (a '' ↑S) := hβv ▸ hull_of_rep a S β hβ0 hβS hβ1
  refine ⟨S, le_antisymm hcard ?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    exact huv.1 (hG2 S (by omega) u v hu.2 hv.2 huS hvS)
  · apply Set.Subset.antisymm
    · rintro y ⟨hy, hyW⟩
      exact core_seg W a huv wt h0 h1 hm y hy hyW
    · exact ((convex_convexHull ℝ _).inter W.convex).segment_subset ⟨huS, hu.2⟩ ⟨hvS, hv.2⟩

theorem supp_cover {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG2 : G2det W a) (I : Finset (Fin n))
    (hI : I.card = d) {u v : EuclideanSpace ℝ (Fin d)} (hne : u ≠ v) (huW : u ∈ W) (hvW : v ∈ W)
    (α β : Fin n → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hαI : ∀ i, i ∉ I → α i = 0) (hα1 : ∑ i, α i = 1)
    (hαu : ∑ i, α i • a i = u) (hβ0 : ∀ i, 0 ≤ β i) (hβI : ∀ i, i ∉ I → β i = 0)
    (hβ1 : ∑ i, β i = 1) (hβv : ∑ i, β i • a i = v) :
    ∀ i ∈ I, 0 < α i + β i := by
  classical
  intro i hi
  by_contra hle
  push_neg at hle
  have hαi : α i = 0 := le_antisymm (by linarith [hβ0 i]) (hα0 i)
  have hβi : β i = 0 := le_antisymm (by linarith [hα0 i]) (hβ0 i)
  have hsub : ∀ j, j ∉ I.erase i → j = i ∨ j ∉ I := by
    intro j hj
    by_cases h : j = i
    · exact Or.inl h
    · exact Or.inr (fun hjI => hj (Finset.mem_erase.2 ⟨h, hjI⟩))
  have hu' : u ∈ convexHull ℝ (a '' ↑(I.erase i)) := hαu ▸ hull_of_rep a _ α hα0
    (fun j hj => (hsub j hj).elim (fun h => h ▸ hαi) (hαI j)) hα1
  have hv' : v ∈ convexHull ℝ (a '' ↑(I.erase i)) := hβv ▸ hull_of_rep a _ β hβ0
    (fun j hj => (hsub j hj).elim (fun h => h ▸ hβi) (hβI j)) hβ1
  have hc : (I.erase i).card + 1 ≤ d := by
    rw [Finset.card_erase_of_mem hi]; have := Finset.card_pos.2 ⟨i, hi⟩; omega
  exact hne (hG2 _ hc u v huW hvW hu' hv')

theorem face_unique {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) (I J : Finset (Fin n)) (hI : I.card = d) (hJ : J.card = d)
    {u v : EuclideanSpace ℝ (Fin d)} (huv : Hirsch.Adj (polygon W a) u v)
    (hIe : convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v)
    (hJe : convexHull ℝ (a '' ↑J) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v) :
    I = J := by
  classical
  have huI : u ∈ convexHull ℝ (a '' ↑I) ∩ (W : Set _) := hIe ▸ left_mem_segment ℝ u v
  have hvI : v ∈ convexHull ℝ (a '' ↑I) ∩ (W : Set _) := hIe ▸ right_mem_segment ℝ u v
  have huJ : u ∈ convexHull ℝ (a '' ↑J) ∩ (W : Set _) := hJe ▸ left_mem_segment ℝ u v
  have hvJ : v ∈ convexHull ℝ (a '' ↑J) ∩ (W : Set _) := hJe ▸ right_mem_segment ℝ u v
  obtain ⟨α, hα0, hαI, hα1, hαu⟩ := hull_rep a I u huI.1
  obtain ⟨β, hβ0, hβI, hβ1, hβv⟩ := hull_rep a I v hvI.1
  obtain ⟨α', hα0', hαJ', hα1', hαu'⟩ := hull_rep a J u huJ.1
  obtain ⟨β', hβ0', hβJ', hβ1', hβv'⟩ := hull_rep a J v hvJ.1
  have hcI := supp_cover W a hG2 I hI huv.1 huI.2 hvI.2 α β hα0 hαI hα1 hαu hβ0 hβI hβ1 hβv
  have hcJ := supp_cover W a hG2 J hJ huv.1 huI.2 hvI.2 α' β' hα0' hαJ' hα1' hαu' hβ0' hβJ'
    hβ1' hβv'
  set wt : Fin n → ℝ := fun i => ((α i + α' i) / 2 + (β i + β' i) / 2) / 2 with hwt
  have h0 : ∀ i, 0 ≤ wt i := fun i => by
    have := hα0 i; have := hβ0 i; have := hα0' i; have := hβ0' i; positivity
  have hu2 : ∑ i, ((α i + α' i) / 2) • a i = u := by
    rw [mid_rep a u u α α' hαu hαu', midpoint_self]
  have hv2 : ∑ i, ((β i + β' i) / 2) • a i = v := by
    rw [mid_rep a v v β β' hβv hβv', midpoint_self]
  have hm : ∑ i, wt i • a i = midpoint ℝ u v := mid_rep a u v _ _ hu2 hv2
  have h1 : ∑ i, wt i = 1 := by
    simp only [hwt, ← Finset.sum_div, Finset.sum_add_distrib, hα1, hβ1, hα1', hβ1']; norm_num
  have hcard := key_card W hW a hG1 huv wt h0 h1 hm
  have hsub : I ∪ J ⊆ Finset.univ.filter (fun i => 0 < wt i) := by
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := hα0 i; have := hβ0 i; have := hα0' i; have := hβ0' i
    rcases Finset.mem_union.1 hi with h | h
    · have := hcI i h; simp only [hwt]; linarith
    · have := hcJ i h; simp only [hwt]; linarith
  have hU : (I ∪ J).card ≤ d := (Finset.card_le_card hsub).trans hcard
  have h1' : I = I ∪ J := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
  have h2' : J = I ∪ J := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
  exact h1'.trans h2'.symm

theorem hA_det {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) :
    (edgeCount (polygon W a) : ℝ≥0∞) ≤
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        {a' | edgeEvent W a' I}.indicator 1 a := by
  classical
  set T := (Finset.univ : Finset (Fin n)).powersetCard d with hT
  have hsum : ∑ I ∈ T, {a' | edgeEvent W a' I}.indicator 1 a =
      ((T.filter (fun I => edgeEvent W a I)).card : ℝ≥0∞) := by
    simp [Set.indicator_apply, Finset.sum_boole]
  rw [hsum]
  have hle : edgeCount (polygon W a) ≤ (T.filter (fun I => edgeEvent W a I)).card := by
    unfold edgeCount
    let f : Set (EuclideanSpace ℝ (Fin d)) → Finset (Fin n) := fun e =>
      if h : ∃ I : Finset (Fin n), I.card = d ∧
          convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = e
      then h.choose else ∅
    have hf : ∀ e ∈ edges (polygon W a), (f e).card = d ∧
        convexHull ℝ (a '' ↑(f e)) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = e := by
      rintro e ⟨u, v, huv, rfl⟩
      have h := face_exists W hW a hG1 hG2 huv
      simp only [f, dif_pos h]
      exact h.choose_spec
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (Finset.finite_toSet _)
    · intro e he
      obtain ⟨hc, heq⟩ := hf e he
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, hc⟩, ?_⟩
      obtain ⟨u, v, huv, rfl⟩ := he
      exact ⟨u, v, huv, heq⟩
    · intro e₁ he₁ e₂ he₂ h
      rw [← (hf e₁ he₁).2, ← (hf e₂ he₂).2, h]
  exact_mod_cast hle

theorem hB_det {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) :
    ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
      {a' | edgeEvent W a' I}.indicator (fun a' => edgeLen W a' I) a ≤
        perimeter (polygon W a) := by
  classical
  set T := (Finset.univ : Finset (Fin n)).powersetCard d with hT
  have hsum : ∑ I ∈ T, {a' | edgeEvent W a' I}.indicator (fun a' => edgeLen W a' I) a =
      ∑ I ∈ T.filter (fun I => edgeEvent W a I), edgeLen W a I := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun I _ => ?_)
    simp [Set.indicator_apply]
  rw [hsum, ← Finset.tsum_subtype]
  have hmem : ∀ I : (T.filter (fun I => edgeEvent W a I)),
      convexHull ℝ (a '' ↑(I : Finset (Fin n))) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) ∈
        edges (polygon W a) := by
    rintro ⟨I, hI⟩
    obtain ⟨u, v, huv, heq⟩ := (Finset.mem_filter.1 hI).2
    exact ⟨u, v, huv, heq⟩
  let φ : (T.filter (fun I => edgeEvent W a I)) → edges (polygon W a) := fun I => ⟨_, hmem I⟩
  have hφ : Function.Injective φ := by
    rintro ⟨I, hI⟩ ⟨J, hJ⟩ h
    have h' : convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) =
        convexHull ℝ (a '' ↑J) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) := congrArg Subtype.val h
    obtain ⟨hIT, u, v, huv, heq⟩ := Finset.mem_filter.1 hI
    have hIc := (Finset.mem_powersetCard.1 hIT).2
    have hJc := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hJ).1).2
    exact Subtype.ext (face_unique W hW a hG1 hG2 I J hIc hJc huv heq (h' ▸ heq))
  unfold perimeter
  exact ENNReal.tsum_comp_le_tsum_of_injective hφ
    (fun e : edges (polygon W a) => Metric.ediam (e : Set (EuclideanSpace ℝ (Fin d))))

theorem bridge1 {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hLI : ∀ t : Fin (d + 1) → Fin n, Function.Injective t →
      LinearIndependent ℝ (fun k : Fin d => a (t k.succ) - a (t 0))) : G1det a := by
  classical
  intro S hS z
  obtain ⟨S', hS'S, hS'c⟩ := Finset.exists_subset_card_eq hS
  set t : Fin (d + 1) → Fin n := fun k => S'.orderEmbOfFin hS'c k with htdef
  have ht : Function.Injective t := (S'.orderEmbOfFin hS'c).injective
  have hmemt : ∀ k, t k ∈ S := fun k => hS'S (Finset.orderEmbOfFin_mem S' hS'c k)
  have hli := hLI t ht
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hz : z ∈ Submodule.span ℝ (Set.range (fun k : Fin d => a (t k.succ) - a (t 0))) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hz
  refine ⟨fun i => (∑ k : Fin d, if t k.succ = i then β k else 0) -
      (if t 0 = i then ∑ k : Fin d, β k else 0),
    ?_, ?_, ?_⟩
  · intro i hi
    have h1 : ∀ k : Fin d, t k.succ ≠ i := fun k h => hi (h ▸ hmemt _)
    have h2 : t 0 ≠ i := fun h => hi (h ▸ hmemt _)
    simp [h1, h2]
  · rw [Finset.sum_sub_distrib, Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  · rw [← hβ]
    simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]

theorem bridge2 {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (w : Fin 2 → EuclideanSpace ℝ (Fin d)) (hwW : ∀ i, w i ∈ W)
    (hLI : ∀ t : Fin (d - 2) → Fin n, Function.Injective t →
      LinearIndependent ℝ (Fin.append w (fun k => a (t k)))) : G2det W a := by
  classical
  intro J hJ x y hxW hyW hx hy
  by_contra hxy
  obtain ⟨Jp, hJJ, -, hJc⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ J)
    (show J.card ≤ d - 1 by omega) (show d - 1 ≤ (Finset.univ : Finset (Fin n)).card by simp; omega)
  obtain ⟨j0, hj0⟩ : Jp.Nonempty := Finset.card_pos.1 (by omega)
  set J' := Jp.erase j0 with hJ'
  have hJ'c : J'.card = d - 2 := by rw [Finset.card_erase_of_mem hj0, hJc]; omega
  set t : Fin (d - 2) → Fin n := fun k => J'.orderEmbOfFin hJ'c k with htdef
  have ht : Function.Injective t := (J'.orderEmbOfFin hJ'c).injective
  have hspan := (hLI t ht).span_eq_top_of_card_eq_finrank' (by simp; omega)
  have hsubJ : convexHull ℝ (a '' ↑J) ⊆ convexHull ℝ (a '' ↑Jp) :=
    convexHull_mono (Set.image_mono (Finset.coe_subset.2 hJJ))
  obtain ⟨α, hα0, hαJ, hα1, hαx⟩ := hull_rep a Jp x (hsubJ hx)
  obtain ⟨β, hβ0, hβJ, hβ1, hβy⟩ := hull_rep a Jp y (hsubJ hy)
  set D := Submodule.span ℝ (↑(J'.image (fun i => a i - a j0)) : Set (EuclideanSpace ℝ (Fin d)))
    with hD
  have hDfin : Module.finrank ℝ D ≤ d - 2 := by
    have h := finrank_span_finset_le_card (R := ℝ) (J'.image (fun i => a i - a j0))
    unfold Set.finrank at h
    exact h.trans (Finset.card_image_le.trans hJ'c.le)
  have hdec : ∀ γ : Fin n → ℝ, (∀ i, i ∉ Jp → γ i = 0) →
      ∑ i, γ i • (a i - a j0) ∈ D := by
    intro γ hγ
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases hi : i ∈ J'
    · exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)))
    · by_cases hi0 : i = j0
      · rw [hi0, sub_self, smul_zero]; exact Submodule.zero_mem _
      · have : i ∉ Jp := fun h => hi (Finset.mem_erase.2 ⟨hi0, h⟩)
        rw [hγ i this, zero_smul]; exact Submodule.zero_mem _
  have hsplit : ∀ γ : Fin n → ℝ,
      ∑ i, γ i • a i = ∑ i, γ i • (a i - a j0) + (∑ i, γ i) • a j0 := by
    intro γ
    simp [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
  have hj0D : a j0 ∈ D ⊔ W := by
    have h := hsplit α
    rw [hαx, hα1, one_smul] at h
    have : a j0 = -(∑ i, α i • (a i - a j0)) + x := by rw [h]; abel
    rw [this]
    exact Submodule.add_mem_sup (D.neg_mem (hdec α hαJ)) hxW
  have htop : D ⊔ W = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    induction j using Fin.addCases with
    | left l =>
      rw [Fin.append_left]; exact Submodule.mem_sup_right (hwW l)
    | right k =>
      rw [Fin.append_right]
      have hk : t k ∈ J' := Finset.orderEmbOfFin_mem J' hJ'c k
      have : a (t k) = (a (t k) - a j0) + a j0 := by abel
      rw [SetLike.mem_coe, this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hk)))) hj0D
  have hgr := Submodule.finrank_sup_add_finrank_inf_eq D W
  rw [htop, finrank_top, finrank_euclideanSpace_fin, hW] at hgr
  have h0 : Module.finrank ℝ ↥(D ⊓ W) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h0
  have hyx : y - x ∈ D ⊓ W := by
    refine ⟨?_, W.sub_mem hyW hxW⟩
    have h := hsplit (fun i => β i - α i)
    have hs0 : ∑ i, (β i - α i) = 0 := by rw [Finset.sum_sub_distrib, hβ1, hα1, sub_self]
    rw [hs0, zero_smul, add_zero] at h
    have hyx' : ∑ i, (β i - α i) • a i = y - x := by
      simp [sub_smul, Finset.sum_sub_distrib, hβy, hαx]
    rw [← hyx', h]
    exact hdec _ (fun i hi => by rw [hβJ i hi, hαJ i hi, sub_self])
  rw [h0] at hyx
  exact hxy (sub_eq_zero.1 ((Submodule.mem_bot ℝ).1 hyx)).symm

end FSFace

namespace STBridge

open MeasureTheory FriendlyShadow.Gaussian SmoothedSimplex.Shadow
open scoped RealInnerProductSpace ENNReal

lemma mem_hull_range_iff' {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    (p : ι → E) (y : E) :
    y ∈ convexHull ℝ (Set.range p) ↔
      ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ ∑ i, μ i • p i = y := by
  classical
  constructor
  · intro hy
    have hsub : convexHull ℝ (Set.range p) ⊆
        {y | ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ ∑ i, μ i • p i = y} := by
      apply convexHull_min
      · rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_, ?_, ?_⟩
        · intro i
          by_cases h : i = j
          · subst h; simp
          · simp [h]
        · simp
        · simp [Pi.single_apply]
      · rintro _ ⟨μ, hμ0, hμ1, rfl⟩ _ ⟨ν, hν0, hν1, rfl⟩ s t hs ht hst
        refine ⟨fun i => s * μ i + t * ν i, fun i => ?_, ?_, ?_⟩
        · have := hμ0 i; have := hν0 i; positivity
        · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, hν1, hst]
        · simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    exact hsub hy
  · rintro ⟨μ, h0, h1, rfl⟩
    exact mem_convexHull_of_exists_fintype μ p h0 h1 (fun i => Set.mem_range_self i) rfl

/-- The graph of a continuously varying finite convex hull is closed. -/
lemma isClosed_hull {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : X → ι → E) (hF : Continuous F) :
    IsClosed {p : X × E | p.2 ∈ convexHull ℝ (Set.range (F p.1))} := by
  have : CompactSpace (stdSimplex ℝ ι) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ ι)
  have hcont : Continuous (fun q : (X × E) × stdSimplex ℝ ι => ∑ i, (q.2 : ι → ℝ) i • F q.1.1 i) :=
    continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).smul
        ((continuous_apply i).comp (hF.comp (continuous_fst.comp continuous_fst))))
  have hC : IsClosed {q : (X × E) × stdSimplex ℝ ι | ∑ i, (q.2 : ι → ℝ) i • F q.1.1 i = q.1.2} :=
    isClosed_eq hcont (continuous_snd.comp continuous_fst)
  have h := isClosedMap_fst_of_compactSpace _ hC
  convert h using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_image, mem_hull_range_iff']
  constructor
  · rintro ⟨μ, h0, h1, h⟩; exact ⟨(p, ⟨μ, h0, h1⟩), h, rfl⟩
  · rintro ⟨⟨p', μ⟩, h, rfl⟩; exact ⟨μ, μ.2.1, μ.2.2, h⟩

/-- The functional certificate of an exposed facet: `⟪φ, aᵢ⟫ = 1` on `I`, `≤ 1` everywhere,
and rows on the hyperplane lie in the facet. -/
def Qc {d n : ℕ} (I : Finset (Fin n)) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ i ∈ I, ⟪φ, a i⟫ = 1) ∧ (∀ j, ⟪φ, a j⟫ ≤ 1) ∧
    (∀ j, ⟪φ, a j⟫ = 1 → a j ∈ convexHull ℝ (a '' ↑I))

lemma inner_comb {d : ℕ} (φ x y : EuclideanSpace ℝ (Fin d)) (s t : ℝ) :
    ⟪φ, s • x + t • y⟫ = s * ⟪φ, x⟫ + t * ⟪φ, y⟫ := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]

lemma convex_H {d : ℕ} (φ : EuclideanSpace ℝ (Fin d)) (F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : Convex ℝ F) : Convex ℝ {y | ⟪φ, y⟫ ≤ 1 ∧ (⟪φ, y⟫ = 1 → y ∈ F)} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  rw [inner_comb]
  refine ⟨by nlinarith [hx.1, hy.1], fun h1 => ?_⟩
  rcases hs.eq_or_lt with hs0 | hs'
  · subst hs0
    have ht1 : t = 1 := by linarith
    subst ht1
    simp only [zero_smul, one_smul, zero_add, zero_mul] at h1 ⊢
    exact hy.2 (by linarith)
  · rcases ht.eq_or_lt with ht0 | ht'
    · subst ht0
      have hs1 : s = 1 := by linarith
      subst hs1
      simp only [zero_smul, one_smul, add_zero, zero_mul] at h1 ⊢
      exact hx.2 (by linarith)
    · have hx1 : ⟪φ, x⟫ = 1 := by nlinarith [hx.1, hy.1]
      have hy1 : ⟪φ, y⟫ = 1 := by nlinarith [hx.1, hy.1]
      exact hF (hx.2 hx1) (hy.2 hy1) hs ht hst

lemma convex_eq1 {d : ℕ} (φ : EuclideanSpace ℝ (Fin d)) :
    Convex ℝ {y : EuclideanSpace ℝ (Fin d) | ⟪φ, y⟫ = 1} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  rw [inner_comb, hx, hy]; linarith

/-- Under `Qc`, the whole polytope `conv(0, a)` lies in `⟪φ,·⟫ ≤ 1`, with the level set
`⟪φ,·⟫ = 1` inside the facet. -/
lemma Q_hull {d n : ℕ} {I : Finset (Fin n)} {a : Fin n → EuclideanSpace ℝ (Fin d)}
    {φ : EuclideanSpace ℝ (Fin d)} (hQ : Qc I a φ) :
    ∀ y ∈ convexHull ℝ (insert 0 (Set.range a)),
      ⟪φ, y⟫ ≤ 1 ∧ (⟪φ, y⟫ = 1 → y ∈ convexHull ℝ (a '' ↑I)) := by
  intro y hy
  have hsub : insert 0 (Set.range a) ⊆
      {y | ⟪φ, y⟫ ≤ 1 ∧ (⟪φ, y⟫ = 1 → y ∈ convexHull ℝ (a '' ↑I))} := by
    rintro _ (rfl | ⟨j, rfl⟩)
    · simp
    · exact ⟨hQ.2.1 j, hQ.2.2 j⟩
  exact convexHull_min hsub (convex_H φ _ (convex_convexHull ℝ _)) hy

lemma Q_face {d n : ℕ} {I : Finset (Fin n)} {a : Fin n → EuclideanSpace ℝ (Fin d)}
    {φ : EuclideanSpace ℝ (Fin d)} (hQ : Qc I a φ) :
    ∀ y ∈ convexHull ℝ (a '' ↑I), ⟪φ, y⟫ = 1 := by
  intro y hy
  have hsub : a '' ↑I ⊆ {y | ⟪φ, y⟫ = 1} := by
    rintro _ ⟨i, hi, rfl⟩; exact hQ.1 i hi
  exact convexHull_min hsub (convex_eq1 φ) hy

lemma face_sub {d n : ℕ} (I : Finset (Fin n)) (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    convexHull ℝ (a '' ↑I) ⊆ convexHull ℝ (insert 0 (Set.range a)) :=
  convexHull_mono (fun _ ⟨i, _, h⟩ => Set.mem_insert_of_mem _ ⟨i, h⟩)

lemma exposed_of_Q {d n : ℕ} {I : Finset (Fin n)} {a : Fin n → EuclideanSpace ℝ (Fin d)}
    {φ : EuclideanSpace ℝ (Fin d)} (hQ : Qc I a φ) :
    IsExposed ℝ (convexHull ℝ (insert 0 (Set.range a))) (convexHull ℝ (a '' ↑I)) := by
  rintro ⟨x0, hx0⟩
  refine ⟨innerSL ℝ φ, ?_⟩
  ext y
  simp only [innerSL_apply_apply, Set.mem_ofPred_eq]
  constructor
  · intro hy
    refine ⟨face_sub I a hy, fun y' hy' => ?_⟩
    rw [Q_face hQ y hy]; exact (Q_hull hQ y' hy').1
  · rintro ⟨hyP, hmax⟩
    have h1 : ⟪φ, y⟫ = 1 := le_antisymm (Q_hull hQ y hyP).1
      ((Q_face hQ x0 hx0).symm.le.trans (hmax x0 (face_sub I a hx0)))
    exact (Q_hull hQ y hyP).2 h1

lemma zero_not_mem {d n : ℕ} {I : Finset (Fin n)} {a : Fin n → EuclideanSpace ℝ (Fin d)}
    (hLI : LinearIndependent ℝ (fun i : I => a i)) :
    (0 : EuclideanSpace ℝ (Fin d)) ∉ convexHull ℝ (a '' ↑I) := by
  intro h0
  obtain ⟨α, hα0, hαI, hα1, hαx⟩ := FSFace.hull_rep a I 0 h0
  have hsum : ∑ i : I, α i • a i = 0 := by
    rw [Finset.sum_coe_sort I (fun i => α i • a i), ← hαx]
    exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [hαI i hi])
  have hz := linearIndependent_iff'.1 hLI Finset.univ (fun i => α i) hsum
  have : ∑ i, α i = 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hαI i hi),
      ← Finset.sum_coe_sort I α]
    exact Finset.sum_eq_zero (fun i _ => hz i (Finset.mem_univ _))
  rw [hα1] at this; exact one_ne_zero this

lemma Q_of_exposed {d n : ℕ} (hd : 1 ≤ d) {I : Finset (Fin n)} (hI : I.card = d)
    {a : Fin n → EuclideanSpace ℝ (Fin d)}
    (hLI : LinearIndependent ℝ (fun i : I => a i))
    (hE : IsExposed ℝ (convexHull ℝ (insert 0 (Set.range a))) (convexHull ℝ (a '' ↑I))) :
    ∃ φ, Qc I a φ := by
  obtain ⟨i0, hi0⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
  have hai : ∀ i ∈ I, a i ∈ convexHull ℝ (a '' ↑I) :=
    fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩
  obtain ⟨l, hl⟩ := hE ⟨a i0, hai i0 hi0⟩
  have hmemF : ∀ x, x ∈ convexHull ℝ (a '' ↑I) ↔
      x ∈ convexHull ℝ (insert 0 (Set.range a)) ∧
        ∀ y ∈ convexHull ℝ (insert 0 (Set.range a)), l y ≤ l x := by
    intro x; rw [hl]; rfl
  have hPa : ∀ j, a j ∈ convexHull ℝ (insert 0 (Set.range a)) :=
    fun j => subset_convexHull ℝ _ (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
  have hP0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (insert 0 (Set.range a)) :=
    subset_convexHull ℝ _ (Set.mem_insert _ _)
  set M := l (a i0) with hM
  have hmax : ∀ y ∈ convexHull ℝ (insert 0 (Set.range a)), l y ≤ M :=
    ((hmemF _).1 (hai i0 hi0)).2
  have hIeq : ∀ i ∈ I, l (a i) = M := fun i hi =>
    le_antisymm (hmax _ (hPa i)) (((hmemF _).1 (hai i hi)).2 _ (hPa i0))
  have hMpos : 0 < M := by
    by_contra hneg
    push_neg at hneg
    apply zero_not_mem hLI
    rw [hmemF]
    refine ⟨hP0, fun y hy => ?_⟩
    rw [map_zero]; exact (hmax y hy).trans hneg
  refine ⟨M⁻¹ • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm l, ?_, ?_, ?_⟩
  · intro i hi
    rw [real_inner_smul_left, InnerProductSpace.toDual_symm_apply, hIeq i hi, inv_mul_cancel₀ hMpos.ne']
  · intro j
    rw [real_inner_smul_left, InnerProductSpace.toDual_symm_apply]
    rw [inv_mul_le_iff₀ hMpos, mul_one]; exact hmax _ (hPa j)
  · intro j hj
    rw [real_inner_smul_left, InnerProductSpace.toDual_symm_apply, inv_mul_eq_one₀ hMpos.ne'] at hj
    rw [hmemF]
    exact ⟨hPa j, fun y hy => hj ▸ hmax y hy⟩

/-- Coefficients of a vector in the basis `(aᵢ)_{i∈I}`. -/
lemma coeffs {d n : ℕ} {I : Finset (Fin n)} (hI : I.card = d)
    {a : Fin n → EuclideanSpace ℝ (Fin d)}
    (hLI : LinearIndependent ℝ (fun i : I => a i)) (v : EuclideanSpace ℝ (Fin d)) :
    ∃ c : Fin n → ℝ, (∀ i, i ∉ I → c i = 0) ∧ ∑ i, c i • a i = v := by
  classical
  have htop := hLI.span_eq_top_of_card_eq_finrank' (by simp [hI])
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1
    (htop ▸ Submodule.mem_top : v ∈ Submodule.span ℝ (Set.range (fun i : I => a i)))
  refine ⟨fun i => if h : i ∈ I then c' ⟨i, h⟩ else 0, fun i hi => by simp [hi], ?_⟩
  rw [← hc']
  calc ∑ i, (if h : i ∈ I then c' ⟨i, h⟩ else 0) • a i
      = ∑ i ∈ I, (if h : i ∈ I then c' ⟨i, h⟩ else 0) • a i :=
        (Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [hi])).symm
    _ = ∑ i : I, (if h : (i : Fin n) ∈ I then c' ⟨i, h⟩ else 0) • a i :=
        (Finset.sum_coe_sort I (fun i => (if h : i ∈ I then c' ⟨i, h⟩ else 0) • a i)).symm
    _ = ∑ i : I, c' i • a i := Finset.sum_congr rfl (fun i _ => by simp [i.2])

/-- (N) a.s. consequence of `g2_ae`: the hull of at most `d-2` rows misses `W` outside `0`. -/
lemma hull_W_zero {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (w : Fin 2 → EuclideanSpace ℝ (Fin d)) (hwW : ∀ i, w i ∈ W)
    (hLI : ∀ t : Fin (d - 2) → Fin n, Function.Injective t →
      LinearIndependent ℝ (Fin.append w (fun k => a (t k))))
    (J : Finset (Fin n)) (hJ : J.card ≤ d - 2) (x : EuclideanSpace ℝ (Fin d))
    (hxW : x ∈ W) (hx : x ∈ convexHull ℝ (a '' ↑J)) : x = 0 := by
  classical
  obtain ⟨Jp, hJJ, -, hJc⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ J)
    hJ (show d - 2 ≤ (Finset.univ : Finset (Fin n)).card by simp; omega)
  set t : Fin (d - 2) → Fin n := fun k => Jp.orderEmbOfFin hJc k with htdef
  have ht : Function.Injective t := (Jp.orderEmbOfFin hJc).injective
  have hspan := (hLI t ht).span_eq_top_of_card_eq_finrank' (by simp; omega)
  set D := Submodule.span ℝ (↑(Jp.image a) : Set (EuclideanSpace ℝ (Fin d))) with hD
  have hDfin : Module.finrank ℝ D ≤ d - 2 := by
    have h := finrank_span_finset_le_card (R := ℝ) (Jp.image a)
    unfold Set.finrank at h
    exact h.trans (Finset.card_image_le.trans hJc.le)
  have htop : D ⊔ W = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    induction j using Fin.addCases with
    | left l =>
      rw [Fin.append_left]; exact Submodule.mem_sup_right (hwW l)
    | right k =>
      rw [Fin.append_right]
      have hk : t k ∈ Jp := Finset.orderEmbOfFin_mem Jp hJc k
      exact Submodule.mem_sup_left (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hk)))
  have hgr := Submodule.finrank_sup_add_finrank_inf_eq D W
  rw [htop, finrank_top, finrank_euclideanSpace_fin, hW] at hgr
  have h0 : Module.finrank ℝ ↥(D ⊓ W) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h0
  have hxD : x ∈ D := by
    obtain ⟨α, -, hαJ, -, hαx⟩ := FSFace.hull_rep a J x hx
    rw [← hαx]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases hi : i ∈ Jp
    · exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)))
    · rw [hαJ i (fun h => hi (hJJ h)), zero_smul]; exact Submodule.zero_mem _
  have : x ∈ D ⊓ W := ⟨hxD, hxW⟩
  rw [h0] at this
  exact (Submodule.mem_bot ℝ).1 this

/-- Characterisation of shadow membership (exact, no general position). -/
lemma mem_shadow_iff {d n : ℕ} (hd : 1 ≤ d) (t z : EuclideanSpace ℝ (Fin d))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (I : Finset (Fin n)) (hI : I.card = d) :
    I ∈ shadow t z a ↔ LinearIndependent ℝ (fun i : I => a i) ∧ (∃ φ, Qc I a φ) ∧
      (convexHull ℝ (a '' ↑I) ∩
        (Submodule.span ℝ {t, z} : Set (EuclideanSpace ℝ (Fin d)))).Nonempty := by
  classical
  simp only [shadow, optSimp, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hqW, hq0, -, hLI, hE, α, hα0, hq⟩
    refine ⟨hLI, Q_of_exposed hd hI hLI hE, ?_⟩
    set s := ∑ i ∈ I, α i with hs
    have hspos : 0 < s := by
      rcases (Finset.sum_nonneg (fun i (_ : i ∈ I) => hα0 i)).eq_or_lt with h | h
      · exfalso; apply hq0
        rw [hq]
        refine Finset.sum_eq_zero (fun i hi => ?_)
        rw [(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hα0 i)).1 h.symm i hi, zero_smul]
      · exact h
    refine ⟨s⁻¹ • q, ?_, Submodule.smul_mem _ _ hqW⟩
    rw [hq, Finset.smul_sum]
    have : ∑ i ∈ I, s⁻¹ • α i • a i = ∑ i ∈ I, (s⁻¹ * α i) • a i := by
      simp [smul_smul]
    rw [this]
    refine (convex_convexHull ℝ _).sum_mem (fun i _ => mul_nonneg (inv_nonneg.2 hspos.le) (hα0 i))
      ?_ (fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩)
    rw [← Finset.mul_sum, ← hs, inv_mul_cancel₀ hspos.ne']
  · rintro ⟨hLI, ⟨φ, hQ⟩, x, hxF, hxW⟩
    refine ⟨x, hxW, fun h => zero_not_mem hLI (h ▸ hxF), hI, hLI, exposed_of_Q hQ, ?_⟩
    obtain ⟨α, hα0, hαI, -, hαx⟩ := FSFace.hull_rep a I x hxF
    refine ⟨α, hα0, ?_⟩
    rw [← hαx]
    exact (Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [hαI i hi])).symm

/-- `{a | (conv(a_I) ∩ W).Nonempty}` is closed. -/
lemma isClosed_meet {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) :
    IsClosed {a : Fin n → EuclideanSpace ℝ (Fin d) |
      (convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))).Nonempty} := by
  have : CompactSpace (stdSimplex ℝ I) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ I)
  have hcont : Continuous (fun q : (Fin n → EuclideanSpace ℝ (Fin d)) × stdSimplex ℝ I =>
      ∑ i : I, (q.2 : I → ℝ) i • q.1 i) :=
    continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).smul
        ((continuous_apply (i : Fin n)).comp continuous_fst))
  have hC : IsClosed {q : (Fin n → EuclideanSpace ℝ (Fin d)) × stdSimplex ℝ I |
      ∑ i : I, (q.2 : I → ℝ) i • q.1 i ∈ W} :=
    (Submodule.closed_of_finiteDimensional W).preimage hcont
  have h := isClosedMap_fst_of_compactSpace _ hC
  convert h using 1
  ext a
  constructor
  · rintro ⟨x, hx, hxW⟩
    rw [Set.image_eq_range] at hx
    obtain ⟨μ, h0, h1, hμ⟩ := (mem_hull_range_iff' (fun i : I => a i) x).1 hx
    refine ⟨(a, ⟨μ, h0, h1⟩), ?_, rfl⟩
    show ∑ i : I, μ i • a i ∈ W
    rw [hμ]; exact hxW
  · rintro ⟨⟨a', μ⟩, hW', rfl⟩
    refine ⟨∑ i : I, (μ : I → ℝ) i • a' i, ?_, hW'⟩
    show _ ∈ convexHull ℝ (a' '' ↑I)
    rw [Set.image_eq_range]
    exact (mem_hull_range_iff' (fun i : I => a' i) _).2 ⟨μ, μ.2.1, μ.2.2, rfl⟩

/-- The certificate set `T` (rows and functional). -/
def Tset {d n : ℕ} (I : Finset (Fin n)) :
    Set ((Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d)) :=
  {p | LinearIndependent ℝ (fun i : I => p.1 i) ∧ Qc I p.1 p.2}

lemma meas_T {d n : ℕ} (I : Finset (Fin n)) : MeasurableSet (Tset (d := d) I) := by
  classical
  have hcontI : Continuous (fun p : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) =>
      fun i : I => p.1 i) :=
    continuous_pi (fun i => (continuous_apply (i : Fin n)).comp continuous_fst)
  have hLI : IsOpen {p : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) |
      LinearIndependent ℝ (fun i : I => p.1 i)} :=
    IsOpen.preimage (f := fun p : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) =>
      fun i : I => p.1 i) hcontI
      (isOpen_setOfPred_linearIndependent :
        IsOpen {f : I → EuclideanSpace ℝ (Fin d) | LinearIndependent ℝ f})
  have hinner : ∀ j : Fin n, Continuous
      (fun p : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) => ⟪p.2, p.1 j⟫) :=
    fun j => continuous_snd.inner ((continuous_apply j).comp continuous_fst)
  have h1 : IsClosed {p : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) |
      ∀ i ∈ I, ⟪p.2, p.1 i⟫ = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _ => isClosed_eq (hinner i) continuous_const))
  have h2 : IsClosed {p : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) |
      ∀ j, ⟪p.2, p.1 j⟫ ≤ 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le (hinner j) continuous_const)
  have hmemj : ∀ j : Fin n, IsClosed
      {p : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) |
        p.1 j ∈ convexHull ℝ (p.1 '' ↑I)} := by
    intro j
    have hc := isClosed_hull
      (fun a : Fin n → EuclideanSpace ℝ (Fin d) => fun i : I => a i)
      (continuous_pi (fun i => continuous_apply _))
    have hpm : Continuous (fun p : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) =>
        (p.1, p.1 j)) := continuous_fst.prodMk ((continuous_apply j).comp continuous_fst)
    have := hc.preimage hpm
    convert this using 1
    ext p
    simp [Set.image_eq_range]
  have h3 : MeasurableSet {p : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) |
      ∀ j, ⟪p.2, p.1 j⟫ = 1 → p.1 j ∈ convexHull ℝ (p.1 '' ↑I)} := by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun j => ?_)
    have : {p : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) |
        ⟪p.2, p.1 j⟫ = 1 → p.1 j ∈ convexHull ℝ (p.1 '' ↑I)} =
        {p | ⟪p.2, p.1 j⟫ = 1}ᶜ ∪ {p | p.1 j ∈ convexHull ℝ (p.1 '' ↑I)} := by
      ext p; simp [imp_iff_not_or]
    rw [this]
    exact ((isClosed_eq (hinner j) continuous_const).measurableSet.compl).union
      (hmemj j).measurableSet
  have : Tset (d := d) I = {p | LinearIndependent ℝ (fun i : I => p.1 i)} ∩
      ({p | ∀ i ∈ I, ⟪p.2, p.1 i⟫ = 1} ∩ ({p | ∀ j, ⟪p.2, p.1 j⟫ ≤ 1} ∩
        {p | ∀ j, ⟪p.2, p.1 j⟫ = 1 → p.1 j ∈ convexHull ℝ (p.1 '' ↑I)})) := by
    ext p; rfl
  rw [this]
  exact hLI.measurableSet.inter (h1.measurableSet.inter (h2.measurableSet.inter h3))

lemma injOn_T {d n : ℕ} (I : Finset (Fin n)) (hI : I.card = d) :
    Set.InjOn Prod.fst (Tset (d := d) I) := by
  rintro ⟨a, φ⟩ ⟨hLI, hQ⟩ ⟨a', φ'⟩ ⟨-, hQ'⟩ hfst
  simp only at hfst
  subst hfst
  dsimp only at hLI hQ hQ'
  have htop := hLI.span_eq_top_of_card_eq_finrank' (by simp [hI])
  have hv : φ - φ' ∈ Submodule.span ℝ (Set.range (fun i : I => a i)) := htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  have h0 : ⟪φ - φ', φ - φ'⟫ = 0 := by
    have h' : ⟪φ - φ', ∑ i, c i • a i⟫ = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [real_inner_smul_right, inner_sub_left, hQ.1 i i.2, hQ'.1 i i.2, sub_self, mul_zero]
    rwa [hc] at h'
  have : φ - φ' = 0 := inner_self_eq_zero.1 h0
  simp only [Prod.mk.injEq, true_and]
  exact sub_eq_zero.1 this

lemma meas_S {d n : ℕ} (hd : 1 ≤ d) (t z : EuclideanSpace ℝ (Fin d)) (I : Finset (Fin n)) :
    MeasurableSet {a : Fin n → EuclideanSpace ℝ (Fin d) | I ∈ shadow t z a} := by
  classical
  by_cases hI : I.card = d
  · have : {a : Fin n → EuclideanSpace ℝ (Fin d) | I ∈ shadow t z a} =
        Prod.fst '' Tset I ∩ {a | (convexHull ℝ (a '' ↑I) ∩
          (Submodule.span ℝ {t, z} : Set (EuclideanSpace ℝ (Fin d)))).Nonempty} := by
      ext a
      rw [Set.mem_ofPred_eq, mem_shadow_iff hd t z a I hI]
      constructor
      · rintro ⟨hLI, ⟨φ, hQ⟩, hne⟩
        exact ⟨⟨(a, φ), ⟨hLI, hQ⟩, rfl⟩, hne⟩
      · rintro ⟨⟨⟨a', φ⟩, ⟨hLI, hQ⟩, rfl⟩, hne⟩
        exact ⟨hLI, ⟨φ, hQ⟩, hne⟩
    rw [this]
    exact ((meas_T I).image_of_continuousOn_injOn continuous_fst.continuousOn
      (injOn_T I hI)).inter (isClosed_meet _ I).measurableSet
  · have : {a : Fin n → EuclideanSpace ℝ (Fin d) | I ∈ shadow t z a} = ∅ := by
      ext a
      simp only [shadow, optSimp, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨q, -, -, hc, -⟩
      exact hI hc
    rw [this]; exact MeasurableSet.empty

lemma measurable_card {d n : ℕ} (hd : 1 ≤ d) (t z : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun a : Fin n → EuclideanSpace ℝ (Fin d) => ((shadow t z a).card : ℝ≥0∞)) := by
  classical
  have h : (fun a : Fin n → EuclideanSpace ℝ (Fin d) => ((shadow t z a).card : ℝ≥0∞)) =
      fun a => ∑ I : Finset (Fin n), {a | I ∈ shadow t z a}.indicator 1 a := by
    funext a
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rw [Finset.sum_boole]
    congr 2
    ext I; simp
  rw [h]
  exact Finset.measurable_sum _ (fun I _ => measurable_const.indicator (meas_S hd t z I))

lemma line_param {d : ℕ} (t z φ x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Submodule.span ℝ {t, z}) (hy : y ∈ Submodule.span ℝ {t, z})
    (hx1 : ⟪φ, x⟫ = 1) (hy1 : ⟪φ, y⟫ = 1) :
    ∃ s : ℝ, y = x + s • (⟪φ, z⟫ • t - ⟪φ, t⟫ • z) := by
  have hyx : y - x ∈ Submodule.span ℝ {t, z} := Submodule.sub_mem _ hy hx
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 hyx
  obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.1 hx
  have h0 : α * ⟪φ, t⟫ + β * ⟪φ, z⟫ = 0 := by
    have : ⟪φ, y - x⟫ = 0 := by rw [inner_sub_right, hx1, hy1, sub_self]
    rw [← hαβ, inner_comb] at this; exact this
  have h1 : γ * ⟪φ, t⟫ + δ * ⟪φ, z⟫ = 1 := by rw [← hγδ, inner_comb] at hx1; exact hx1
  have hy' : y = x + (α • t + β • z) := by rw [hαβ]; abel
  have key : ∀ s : ℝ, α = s * ⟪φ, z⟫ → β = -(s * ⟪φ, t⟫) →
      y = x + s • (⟪φ, z⟫ • t - ⟪φ, t⟫ • z) := by
    intro s ha hb
    rw [hy', ha, hb]
    congr 1
    rw [smul_sub, smul_smul, smul_smul, neg_smul, ← sub_eq_add_neg]
  by_cases ht : ⟪φ, t⟫ = 0
  · have hz : ⟪φ, z⟫ ≠ 0 := by
      intro hz; rw [ht, hz] at h1; simp at h1
    have hβ : β = 0 := by
      rw [ht, mul_zero, zero_add] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h hz
    refine ⟨α / ⟪φ, z⟫, key _ (by field_simp) (by rw [ht, hβ]; ring)⟩
  · refine ⟨-β / ⟪φ, t⟫, key _ ?_ (by field_simp)⟩
    field_simp
    linarith

lemma edge_of_shadow {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (t z : EuclideanSpace ℝ (Fin d)) (hzt : LinearIndependent ℝ ![z, t])
    (hW : Module.finrank ℝ (Submodule.span ℝ {t, z}) = 2)
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hLI2 : ∀ s : Fin (d - 2) → Fin n, Function.Injective s →
      LinearIndependent ℝ (Fin.append ![z, t] (fun k => a (s k))))
    (I : Finset (Fin n)) (hI : I.card = d) (hLI : LinearIndependent ℝ (fun i : I => a i))
    (φ : EuclideanSpace ℝ (Fin d)) (hQ : Qc I a φ) (x : EuclideanSpace ℝ (Fin d))
    (hxF : x ∈ convexHull ℝ (a '' ↑I)) (hxW : x ∈ Submodule.span ℝ {t, z}) :
    edgeEvent (Submodule.span ℝ {t, z}) a I := by
  classical
  set W := Submodule.span ℝ {t, z} with hWdef
  set K := convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) with hK
  set e := ⟪φ, z⟫ • t - ⟪φ, t⟫ • z with he
  have htW : t ∈ W := Submodule.subset_span (by simp)
  have hzW : z ∈ W := Submodule.subset_span (by simp)
  have hwW : ∀ i, (![z, t] : Fin 2 → EuclideanSpace ℝ (Fin d)) i ∈ W := by
    intro i; fin_cases i
    · exact hzW
    · exact htW
  have heW : e ∈ W := W.sub_mem (W.smul_mem _ htW) (W.smul_mem _ hzW)
  have hφe : ⟪φ, e⟫ = 0 := by
    rw [he, inner_sub_right, real_inner_smul_right, real_inner_smul_right]; ring
  have hx1 : ⟪φ, x⟫ = 1 := Q_face hQ x hxF
  have he0 : e ≠ 0 := by
    intro h0
    have hcomb : -⟪φ, t⟫ • z + ⟪φ, z⟫ • t = 0 := by
      rw [← h0, he]; module
    have hpair := LinearIndependent.pair_iff.1 hzt (-⟪φ, t⟫) ⟪φ, z⟫ hcomb
    obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.1 hxW
    rw [← hγδ, inner_comb] at hx1
    have h1 : ⟪φ, t⟫ = 0 := by linarith [hpair.1]
    rw [h1, hpair.2] at hx1; simp at hx1
  obtain ⟨w, hw0, hwI, hw1, hwx⟩ := FSFace.hull_rep a I x hxF
  obtain ⟨c, hcI, hce⟩ := coeffs hI hLI e
  have hcsum : ∑ i, c i = 0 := by
    have : ⟪φ, ∑ i, c i • a i⟫ = ∑ i, c i := by
      rw [inner_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_smul_right]
      by_cases hi : i ∈ I
      · rw [hQ.1 i hi, mul_one]
      · rw [hcI i hi, zero_mul]
    rw [← this, hce, hφe]
  have hnotwo : ∀ i k, i ∈ I → k ∈ I → i ≠ k → w i = 0 → w k = 0 → False := by
    intro i k hi hk hik hwi hwk
    set J := Finset.univ.filter (fun j => 0 < w j) with hJ
    have hJsub : J ⊆ (I.erase i).erase k := by
      intro j hj
      have hj' : 0 < w j := (Finset.mem_filter.1 hj).2
      have hjI : j ∈ I := by
        by_contra h; rw [hwI j h] at hj'; exact lt_irrefl _ hj'
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hjI⟩⟩
      · rintro rfl; rw [hwk] at hj'; exact lt_irrefl _ hj'
      · rintro rfl; rw [hwi] at hj'; exact lt_irrefl _ hj'
    have hJc : J.card ≤ d - 2 := by
      have := Finset.card_le_card hJsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hik.symm, hk⟩),
        Finset.card_erase_of_mem hi, hI] at this
      omega
    have hxJ : x ∈ convexHull ℝ (a '' ↑J) := by
      rw [← hwx]
      refine FSFace.hull_of_rep a J w hw0 (fun j hj => ?_) hw1
      have : ¬ 0 < w j := fun h => hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      exact le_antisymm (not_lt.1 this) (hw0 j)
    have hx0 := hull_W_zero hd hdn W hW a ![z, t] hwW hLI2 J hJc x hxW hxJ
    exact zero_not_mem hLI (hx0 ▸ hxF)
  obtain ⟨σ, hσ, hσneg⟩ : ∃ σ : ℝ, σ ≠ 0 ∧ ∀ i, σ * c i < 0 → 0 < w i := by
    by_cases hA : ∀ i, c i ≠ 0 → 0 < w i
    · refine ⟨1, one_ne_zero, fun i h => hA i ?_⟩
      intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
    · push_neg at hA
      obtain ⟨k, hck, hwk⟩ := hA
      have hwk0 : w k = 0 := le_antisymm hwk (hw0 k)
      have hkI : k ∈ I := by by_contra h; exact hck (hcI k h)
      refine ⟨c k, hck, fun i hi => ?_⟩
      by_contra hwi
      have hwi0 : w i = 0 := le_antisymm (not_lt.1 hwi) (hw0 i)
      have hci : c i ≠ 0 := by intro h0; rw [h0, mul_zero] at hi; exact lt_irrefl _ hi
      have hiI : i ∈ I := by by_contra h; exact hci (hcI i h)
      have hik : i ≠ k := by
        rintro rfl; exact absurd hi (not_lt.2 (mul_self_nonneg _))
      exact hnotwo i k hiI hkI hik hwi0 hwk0
  obtain ⟨ε, hε, hεw⟩ := FSFace.pert_eps w (fun i => min (σ * c i) 0) hw0 (fun i hi => hσneg i (by
      by_contra h; push_neg at h; exact hi (min_eq_right h)))
  set w' : Fin n → ℝ := fun i => w i + ε * (σ * c i) with hw'
  have hw'0 : ∀ i, 0 ≤ w' i := fun i => by
    have h1 := hεw i
    have hm : min (σ * c i) 0 ≤ σ * c i := min_le_left _ _
    have : ε * min (σ * c i) 0 ≤ ε * (σ * c i) := mul_le_mul_of_nonneg_left hm hε.le
    simp only [hw']; linarith
  have hw'I : ∀ i, i ∉ I → w' i = 0 := fun i hi => by simp [hw', hwI i hi, hcI i hi]
  have hw'1 : ∑ i, w' i = 1 := by
    have : ∑ i, ε * (σ * c i) = ε * (σ * ∑ i, c i) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    simp only [hw', Finset.sum_add_distrib, this, hw1, hcsum, mul_zero, add_zero]
  have hx'eq : ∑ i, w' i • a i = x + (ε * σ) • e := by
    simp only [hw', add_smul, Finset.sum_add_distrib, hwx]
    congr 1
    rw [← hce, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_smul, mul_assoc]
  have hx'F : x + (ε * σ) • e ∈ convexHull ℝ (a '' ↑I) :=
    hx'eq ▸ FSFace.hull_of_rep a I w' hw'0 hw'I hw'1
  have hx'W : x + (ε * σ) • e ∈ W := W.add_mem hxW (W.smul_mem _ heW)
  have hx'ne : x + (ε * σ) • e ≠ x := by
    intro h
    have h' : (ε * σ) • e = 0 := by
      have := congrArg (fun y => y - x) h
      simpa using this
    rcases smul_eq_zero.1 h' with h1 | h1
    · exact mul_ne_zero hε.ne' hσ h1
    · exact he0 h1
  have hKc : IsCompact K :=
    ((I.finite_toSet.image a).isCompact_convexHull (𝕜 := ℝ)).inter_right
      (Submodule.closed_of_finiteDimensional W)
  have hxK : x ∈ K := ⟨hxF, hxW⟩
  have hcont : ContinuousOn (fun y : EuclideanSpace ℝ (Fin d) => ⟪y, e⟫) K :=
    (continuous_id.inner continuous_const).continuousOn
  obtain ⟨u, huK, humin⟩ := hKc.exists_isMinOn ⟨x, hxK⟩ hcont
  obtain ⟨v, hvK, hvmax⟩ := hKc.exists_isMaxOn ⟨x, hxK⟩ hcont
  have hpar : ∀ y ∈ K, ∃ s : ℝ, y = x + s • e := fun y hy =>
    line_param t z φ x y hxW hy.2 hx1 (Q_face hQ y hy.1)
  have hfe : ∀ s : ℝ, ⟪x + s • e, e⟫ = ⟪x, e⟫ + s * ‖e‖ ^ 2 := by
    intro s; rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hepos : 0 < ‖e‖ ^ 2 := pow_pos (norm_pos_iff.2 he0) 2
  obtain ⟨su, hu⟩ := hpar u huK
  obtain ⟨sv, hv⟩ := hpar v hvK
  have hKseg : K = segment ℝ u v := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨s, hs⟩ := hpar y hy
      have h1 : ⟪u, e⟫ ≤ ⟪y, e⟫ := humin hy
      have h2 : ⟪y, e⟫ ≤ ⟪v, e⟫ := hvmax hy
      rw [hu, hs, hfe, hfe] at h1
      rw [hv, hs, hfe, hfe] at h2
      have hsu : su ≤ s := by nlinarith
      have hsv : s ≤ sv := by nlinarith
      rcases hsu.eq_or_lt with heq | hlt
      · rw [hs, ← heq, ← hu]; exact left_mem_segment ℝ u v
      · have hpos : 0 < sv - su := by linarith
        refine ⟨(sv - s) / (sv - su), (s - su) / (sv - su), div_nonneg (by linarith) hpos.le,
          div_nonneg (by linarith) hpos.le, by field_simp; ring, ?_⟩
        have hcomb : (sv - s) / (sv - su) * su + (s - su) / (sv - su) * sv = s := by
          field_simp; ring
        have hAB : (sv - s) / (sv - su) + (s - su) / (sv - su) = 1 := by field_simp; ring
        rw [hu, hv, hs]
        calc ((sv - s) / (sv - su)) • (x + su • e) + ((s - su) / (sv - su)) • (x + sv • e)
            = ((sv - s) / (sv - su) + (s - su) / (sv - su)) • x +
                ((sv - s) / (sv - su) * su + (s - su) / (sv - su) * sv) • e := by module
          _ = x + s • e := by rw [hAB, hcomb, one_smul]
    · exact ((convex_convexHull ℝ _).inter W.convex).segment_subset huK hvK
  have huv : u ≠ v := by
    intro h
    rw [h, segment_same] at hKseg
    have h1 : x ∈ ({v} : Set (EuclideanSpace ℝ (Fin d))) := hKseg ▸ hxK
    have h2 : x + (ε * σ) • e ∈ ({v} : Set (EuclideanSpace ℝ (Fin d))) := hKseg ▸ ⟨hx'F, hx'W⟩
    exact hx'ne ((Set.mem_singleton_iff.1 h2).trans (Set.mem_singleton_iff.1 h1).symm)
  refine ⟨u, v, ⟨huv, ?_⟩, hKseg⟩
  rw [← hKseg]
  show IsExtreme ℝ (convexHull ℝ (Set.range a) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))) K
  apply IsExposed.isExtreme
  rintro -
  refine ⟨innerSL ℝ φ, ?_⟩
  ext y
  simp only [innerSL_apply_apply]
  constructor
  · rintro ⟨hyF, hyW⟩
    refine ⟨⟨convexHull_mono (Set.image_subset_range a _) hyF, hyW⟩, fun y' hy' => ?_⟩
    rw [Q_face hQ y hyF]
    exact (Q_hull hQ y' (convexHull_mono (Set.subset_insert _ _) hy'.1)).1
  · rintro ⟨hyP, hmax⟩
    have hyP' := convexHull_mono (Set.subset_insert 0 (Set.range a)) hyP.1
    have h1 : ⟪φ, y⟫ = 1 := le_antisymm (Q_hull hQ y hyP').1
      (hx1.symm.le.trans (hmax x ⟨convexHull_mono (Set.image_subset_range a _) hxF, hxW⟩))
    exact ⟨(Q_hull hQ y hyP').2 h1, hyP.2⟩

lemma card_le_edgeCount {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hG1 : FSFace.G1det a) (hG2 : FSFace.G2det W a)
    (S : Finset (Finset (Fin n))) (hS : ∀ I ∈ S, I.card = d ∧ edgeEvent W a I) :
    S.card ≤ edgeCount (polygon W a) := by
  classical
  let f : Finset (Fin n) → Set (EuclideanSpace ℝ (Fin d)) :=
    fun I => convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))
  have hfin : (edges (polygon W a)).Finite := by
    refine (Set.finite_univ.image f).subset ?_
    rintro _ ⟨u, v, huv, rfl⟩
    obtain ⟨I, -, hI⟩ := FSFace.face_exists W hW a hG1 hG2 huv
    exact ⟨I, Set.mem_univ _, hI⟩
  unfold edgeCount
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn f ?_ ?_ hfin
  · intro I hI
    obtain ⟨-, u, v, huv, heq⟩ := hS I hI
    exact ⟨u, v, huv, heq⟩
  · intro I hI J hJ hIJ
    obtain ⟨hIc, u, v, huv, heq⟩ := hS I hI
    have hJc := (hS J hJ).1
    exact FSFace.face_unique W hW a hG1 hG2 I J hIc hJc huv heq
      (show f J = segment ℝ u v from hIJ.symm.trans heq)

lemma card_of_mem {d n : ℕ} {t z : EuclideanSpace ℝ (Fin d)} {a : Fin n → EuclideanSpace ℝ (Fin d)}
    {I : Finset (Fin n)} (h : I ∈ shadow t z a) : I.card = d := by
  classical
  simp only [shadow, optSimp, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨q, -, -, hc, -⟩ := h
  exact hc

theorem main {d n : ℕ} (hd : 3 ≤ d) (hn : d ≤ n)
    (z t : EuclideanSpace ℝ (Fin d)) (hzt : LinearIndependent ℝ ![z, t])
    (σ : ℝ) (abar : Fin n → EuclideanSpace ℝ (Fin d)) :
    AEMeasurable (fun a => ((shadow t z a).card : ℝ≥0∞))
        (Measure.pi (fun i => gaussian (abar i) σ)) ∧
      ∀ᵐ a ∂(Measure.pi (fun i => gaussian (abar i) σ)),
        (shadow t z a).card ≤ edgeCount (polygon (Submodule.span ℝ {t, z}) a) := by
  refine ⟨(measurable_card (by omega) t z).aemeasurable, ?_⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hW : Module.finrank ℝ (Submodule.span ℝ {t, z}) = 2 := by
    have h := finrank_span_eq_card hzt
    have hr : Set.range ![z, t] = {t, z} := by
      ext x; simp [Fin.exists_fin_two, eq_comm, or_comm]
    rw [hr] at h; simpa using h
  have hwW : ∀ i, (![z, t] : Fin 2 → EuclideanSpace ℝ (Fin d)) i ∈ Submodule.span ℝ {t, z} := by
    intro i; fin_cases i
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  change ∀ᵐ a ∂(rowLaw (fun i => gaussianPdf (abar i) σ)), _
  filter_upwards [FSGP.g1_ae (fun i => gaussianPdf (abar i) σ),
    FSGP.g2_ae (by omega) (fun i => gaussianPdf (abar i) σ) _ hzt] with a h1 h2
  have hG1 := FSFace.bridge1 a h1
  have hG2 := FSFace.bridge2 hd hn _ hW a _ hwW h2
  refine card_le_edgeCount _ hW a hG1 hG2 _ (fun I hI => ?_)
  have hIc : I.card = d := card_of_mem hI
  obtain ⟨hLI, ⟨φ, hQ⟩, x, hxF, hxW⟩ := (mem_shadow_iff (by omega) t z a I hIc).1 hI
  exact ⟨hIc, edge_of_shadow hd hn t z hzt hW a h2 I hIc hLI φ hQ x hxF hxW⟩

end STBridge

open MeasureTheory SmoothedSimplex.Shadow in
theorem solution {d n : ℕ} (hd : 3 ≤ d) (hn : d ≤ n)
    (z t : EuclideanSpace ℝ (Fin d)) (hzt : LinearIndependent ℝ ![z, t])
    (σ : ℝ) (hσ : 0 < σ) (abar : Fin n → EuclideanSpace ℝ (Fin d)) :
    AEMeasurable (fun a => ((shadow t z a).card : ENNReal))
        (Measure.pi (fun i => gaussian (abar i) σ)) ∧
      ∀ᵐ a ∂(Measure.pi (fun i => gaussian (abar i) σ)),
        (shadow t z a).card ≤
          FriendlyShadow.Gaussian.edgeCount
            (FriendlyShadow.Gaussian.polygon (Submodule.span ℝ {t, z}) a) := by
  exact STBridge.main hd hn z t hzt σ abar
