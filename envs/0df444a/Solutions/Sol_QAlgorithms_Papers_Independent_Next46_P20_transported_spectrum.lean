-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P20.transported_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:18:51.44066+00:00
-- url     : https://prove2.me/submissions/fad408e6-2706-4aea-ba59-54bb3bc978cc

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20
noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

open QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-! ### g62h tensor library: tensorEmbedding is the genuine L2 tensor map -/

def g62h_idx (n : ℕ) : Fin n × Fin 2 ≃ Fin n ⊕ Fin n where
  toFun q := if q.2 = 0 then Sum.inl q.1 else Sum.inr q.1
  invFun s := Sum.elim (fun j => (j, 0)) (fun j => (j, 1)) s
  left_inv q := by rcases q with ⟨j, a⟩; fin_cases a <;> rfl
  right_inv s := by rcases s with j | j <;> rfl

def g62h_e (n : ℕ) : PhaseCoordinates n ≃ᵐ Configuration n × Configuration n :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (g62h_idx n)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))

lemma g62h_e_apply {n : ℕ} (z : PhaseCoordinates n) :
    g62h_e n z = (phasePosition z, phaseMomentum z) := by
  ext j
  · show (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (g62h_idx n) z) (Sum.inl j) = z (j, 0)
    have : (Sum.inl j : Fin n ⊕ Fin n) = g62h_idx n (j, 0) := rfl
    rw [this, MeasurableEquiv.piCongrLeft_apply_apply]
  · show (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (g62h_idx n) z) (Sum.inr j) = z (j, 1)
    have : (Sum.inr j : Fin n ⊕ Fin n) = g62h_idx n (j, 1) := rfl
    rw [this, MeasurableEquiv.piCongrLeft_apply_apply]

lemma g62h_e_mp (n : ℕ) : MeasurePreserving (g62h_e n) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (g62h_idx n))

lemma g62h_qmp_pos (n : ℕ) :
    Measure.QuasiMeasurePreserving (phasePosition (n := n)) volume volume := by
  have h := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Configuration n)))
    (ν := (volume : Measure (Configuration n)))).comp (g62h_e_mp n).quasiMeasurePreserving
  have e : (Prod.fst ∘ g62h_e n) = phasePosition := by funext z; simp [g62h_e_apply]
  rw [e] at h; exact h

lemma g62h_qmp_mom (n : ℕ) :
    Measure.QuasiMeasurePreserving (phaseMomentum (n := n)) volume volume := by
  have h := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Configuration n)))
    (ν := (volume : Measure (Configuration n)))).comp (g62h_e_mp n).quasiMeasurePreserving
  have e : (Prod.snd ∘ g62h_e n) = phaseMomentum := by funext z; simp [g62h_e_apply]
  rw [e] at h; exact h

def g62h_G {n : ℕ} (chi psi : ConfigurationL2 n) : Configuration n × Configuration n → ℂ :=
  fun q => psi q.1 * star (chi q.2)

def g62h_F {n : ℕ} (chi psi : ConfigurationL2 n) : PhaseCoordinates n → ℂ :=
  fun z => psi (phasePosition z) * star (chi (phaseMomentum z))

lemma g62h_F_eq {n : ℕ} (chi psi : ConfigurationL2 n) : g62h_F chi psi = g62h_G chi psi ∘ g62h_e n := by
  funext z; simp [g62h_F, g62h_G, g62h_e_apply]

lemma g62h_G_memLp {n : ℕ} (chi psi : ConfigurationL2 n) :
    MemLp (g62h_G chi psi) 2 (volume : Measure (Configuration n × Configuration n)) := by
  have hm : AEStronglyMeasurable (g62h_G chi psi)
      (volume : Measure (Configuration n × Configuration n)) :=
    (Lp.aestronglyMeasurable psi).comp_fst.mul (Lp.aestronglyMeasurable chi).comp_snd.star
  rw [memLp_two_iff_integrable_sq_norm hm]
  have h1 := (Lp.memLp psi).integrable_norm_pow (p := 2) (by norm_num)
  have h2 := (Lp.memLp chi).integrable_norm_pow (p := 2) (by norm_num)
  have := h1.mul_prod h2
  refine this.congr (Filter.Eventually.of_forall (fun q => ?_))
  simp [g62h_G, mul_pow]

lemma g62h_F_memLp {n : ℕ} (chi psi : ConfigurationL2 n) :
    MemLp (g62h_F chi psi) 2 (volume : Measure (PhaseCoordinates n)) := by
  rw [g62h_F_eq]; exact (g62h_G_memLp chi psi).comp_measurePreserving (g62h_e_mp n)

lemma g62h_F_inner {n : ℕ} (chi psi chi' psi' : ConfigurationL2 n) :
    ∫ z, star (g62h_F chi psi z) * g62h_F chi' psi' z =
      inner ℂ psi psi' * inner ℂ chi' chi := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h3 := (g62h_e_mp n).integral_comp' (G := ℂ) (fun q : Configuration n × Configuration n =>
        (star (psi q.1) * psi' q.1) * (star (chi' q.2) * chi q.2))
  simp only [g62h_e_apply] at h3
  have h4 : ∫ z, star (g62h_F chi psi z) * g62h_F chi' psi' z =
      ∫ z, (star (psi (phasePosition z)) * psi' (phasePosition z)) *
        (star (chi' (phaseMomentum z)) * chi (phaseMomentum z)) := by
    congr 1; funext z; simp [g62h_F]; ring
  rw [h4, h3]
  have h := integral_prod_mul (μ := (volume : Measure (Configuration n)))
    (ν := (volume : Measure (Configuration n)))
    (fun x => star (psi x) * psi' x) (fun p => star (chi' p) * chi p)
  simp only [RCLike.inner_apply, starRingEnd_apply]
  refine h.trans ?_
  congr 1 <;> (congr 1; funext x; ring)

def g62h_Tl {n : ℕ} (chi : ConfigurationL2 n) : ConfigurationL2 n →ₗ[ℂ] PhaseL2 n where
  toFun psi := MemLp.toLp _ (g62h_F_memLp chi psi)
  map_add' psi phi := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [(g62h_qmp_pos n).ae (Lp.coeFn_add psi phi)] with z hz
    simp only [g62h_F, Pi.add_apply]; rw [hz]; simp only [Pi.add_apply]; ring
  map_smul' c psi := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [(g62h_qmp_pos n).ae (Lp.coeFn_smul c psi)] with z hz
    simp only [g62h_F, Pi.smul_apply]; rw [hz]; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma g62h_Tl_ae {n : ℕ} (chi psi : ConfigurationL2 n) :
    (g62h_Tl chi psi : PhaseCoordinates n → ℂ) =ᵐ[volume] g62h_F chi psi :=
  MemLp.coeFn_toLp (g62h_F_memLp chi psi)

lemma g62h_Tl_inner {n : ℕ} (chi psi chi' psi' : ConfigurationL2 n) :
    inner ℂ (g62h_Tl chi psi) (g62h_Tl chi' psi') = inner ℂ psi psi' * inner ℂ chi' chi := by
  rw [MeasureTheory.L2.inner_def, ← g62h_F_inner]
  apply integral_congr_ae
  filter_upwards [g62h_Tl_ae chi psi, g62h_Tl_ae chi' psi'] with z h1 h2
  rw [RCLike.inner_apply, h1, h2]; simp only [starRingEnd_apply]; ring

lemma g62h_Tl_norm {n : ℕ} (chi psi : ConfigurationL2 n) :
    ‖g62h_Tl chi psi‖ = ‖psi‖ * ‖chi‖ := by
  have h := g62h_Tl_inner chi psi chi psi
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖g62h_Tl chi psi‖ ^ 2 = (‖psi‖ * ‖chi‖) ^ 2 := by
    rw [mul_pow]; exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'

def g62h_T {n : ℕ} (chi : ConfigurationL2 n) : ConfigurationL2 n →L[ℂ] PhaseL2 n :=
  (g62h_Tl chi).mkContinuous ‖chi‖ (fun psi => by rw [g62h_Tl_norm, mul_comm])

lemma g62h_T_realizes {n : ℕ} (chi : ConfigurationL2 n) : RealizesTensor chi (g62h_T chi) :=
  fun psi => g62h_Tl_ae chi psi

lemma g62h_tensor_eq {n : ℕ} (chi : ConfigurationL2 n) : tensorEmbedding chi = g62h_T chi := by
  have hex : ∃ T : ConfigurationL2 n →L[ℂ] PhaseL2 n, RealizesTensor chi T :=
    ⟨_, g62h_T_realizes chi⟩
  unfold tensorEmbedding
  rw [dif_pos hex]
  ext1 psi
  apply Lp.ext
  filter_upwards [Classical.choose_spec hex psi, g62h_T_realizes chi psi] with z h1 h2
  rw [h1, h2]

lemma g62h_tensor_ae {n : ℕ} (chi psi : ConfigurationL2 n) :
    (tensorEmbedding chi psi : PhaseCoordinates n → ℂ) =ᵐ[volume] g62h_F chi psi := by
  rw [g62h_tensor_eq]; exact g62h_T_realizes chi psi

lemma g62h_tensor_realizes {n : ℕ} (chi : ConfigurationL2 n) :
    RealizesTensor chi (tensorEmbedding chi) := by
  rw [g62h_tensor_eq]; exact g62h_T_realizes chi

lemma g62h_tensor_inner {n : ℕ} (chi psi chi' psi' : ConfigurationL2 n) :
    inner ℂ (tensorEmbedding chi psi) (tensorEmbedding chi' psi') =
      inner ℂ psi psi' * inner ℂ chi' chi := by
  rw [g62h_tensor_eq, g62h_tensor_eq]; exact g62h_Tl_inner chi psi chi' psi'

lemma g62h_tensor_norm {n : ℕ} (chi psi : ConfigurationL2 n) :
    ‖tensorEmbedding chi psi‖ = ‖psi‖ * ‖chi‖ := by
  rw [g62h_tensor_eq]; exact g62h_Tl_norm chi psi

lemma g62h_inner1 {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) (psi phi : ConfigurationL2 n) :
    inner ℂ (tensorEmbedding chi psi) (tensorEmbedding chi phi) = inner ℂ psi phi := by
  rw [g62h_tensor_inner, inner_self_eq_norm_sq_to_K, hchi]; simp

lemma g62h_norm1 {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) (psi : ConfigurationL2 n) :
    ‖tensorEmbedding chi psi‖ = ‖psi‖ := by
  rw [g62h_tensor_norm, hchi, mul_one]

lemma g62h_inj {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) :
    Function.Injective (tensorEmbedding chi) := by
  intro a b h
  have : ‖tensorEmbedding chi (a - b)‖ = 0 := by rw [map_sub, h, sub_self, norm_zero]
  rw [g62h_norm1 chi hchi] at this
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

lemma g62h_adj_T {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) (psi : ConfigurationL2 n) :
    (tensorEmbedding chi).adjoint (tensorEmbedding chi psi) = psi := by
  apply ext_inner_right ℂ
  intro phi
  rw [ContinuousLinearMap.adjoint_inner_left, g62h_inner1 chi hchi]

lemma g62h_adj_comp {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) :
    (tensorEmbedding chi).adjoint.comp (tensorEmbedding chi) = 1 := by
  ext1 psi; simp [g62h_adj_T chi hchi]

lemma g62h_T_adj_mem {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) (Psi : PhaseL2 n)
    (h : Psi ∈ windowSpace chi) : tensorEmbedding chi ((tensorEmbedding chi).adjoint Psi) = Psi := by
  obtain ⟨psi, rfl⟩ := h
  simp [g62h_adj_T chi hchi]

def g62h_Ui {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) :
    ConfigurationL2 n →ₗᵢ[ℂ] windowSpace chi where
  toLinearMap := (tensorEmbedding chi).toLinearMap.rangeRestrict
  norm_map' psi := by
    show ‖tensorEmbedding chi psi‖ = ‖psi‖
    exact g62h_norm1 chi hchi psi

def g62h_U {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) :
    ConfigurationL2 n ≃ₗᵢ[ℂ] windowSpace chi :=
  LinearIsometryEquiv.ofSurjective (g62h_Ui chi hchi) (LinearMap.surjective_rangeRestrict _)

lemma g62h_U_apply {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) (psi : ConfigurationL2 n) :
    (g62h_U chi hchi psi : PhaseL2 n) = tensorEmbedding chi psi := rfl

lemma g62h_U_symm {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) (Psi : windowSpace chi) :
    (g62h_U chi hchi).symm Psi = (tensorEmbedding chi).adjoint Psi := by
  apply (g62h_U chi hchi).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [g62h_U_apply, g62h_T_adj_mem chi hchi _ Psi.2]

lemma g62h_tG_mem {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1)
    (G : Set (ConfigurationL2 n × ConfigurationL2 n)) (psi eta : ConfigurationL2 n) :
    (tensorEmbedding chi psi, tensorEmbedding chi eta) ∈ transportGraph chi G ↔ (psi, eta) ∈ G := by
  constructor
  · rintro ⟨u, v, h, h1, h2⟩
    rw [g62h_inj chi hchi h1, g62h_inj chi hchi h2] at h; exact h
  · intro h; exact ⟨psi, eta, h, rfl, rfl⟩

lemma g62h_tG_eq {n : ℕ} (chi : ConfigurationL2 n)
    (G : Set (ConfigurationL2 n × ConfigurationL2 n)) :
    transportGraph chi G = Prod.map (tensorEmbedding chi) (tensorEmbedding chi) '' G := by
  ext ⟨a, b⟩
  simp only [transportGraph, Set.mem_setOf_eq, Set.mem_image, Prod.exists, Prod.map, Prod.mk.injEq]

lemma g62h_iso {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) :
    Isometry (tensorEmbedding chi) :=
  AddMonoidHomClass.isometry_of_norm _ (g62h_norm1 chi hchi)

lemma g62h_window_coe {n : ℕ} (chi : ConfigurationL2 n) :
    (windowSpace chi : Set (PhaseL2 n)) = tensorEmbedding chi '' Set.univ := by
  rw [Set.image_univ]; rfl

lemma g62h_adjG {n : ℕ} (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1)
    (G : Set (ConfigurationL2 n × ConfigurationL2 n)) :
    adjointGraphOn (windowSpace chi) (Prod.map (tensorEmbedding chi) (tensorEmbedding chi) '' G) =
      Prod.map (tensorEmbedding chi) (tensorEmbedding chi) ''
        adjointGraphOn (⊤ : Submodule ℂ (ConfigurationL2 n)) G := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩, h⟩
    have hx' : tensorEmbedding chi x = a := hx
    have hy' : tensorEmbedding chi y = b := hy
    refine ⟨(x, y), ⟨trivial, trivial, fun u v huv => ?_⟩, ?_⟩
    · have := h (tensorEmbedding chi u) (tensorEmbedding chi v) ⟨(u, v), huv, rfl⟩
      simp only at this
      rwa [← hx', ← hy', g62h_inner1 chi hchi, g62h_inner1 chi hchi] at this
    · simp [Prod.map, ← hx', ← hy']
  · rintro ⟨⟨x, y⟩, ⟨-, -, h⟩, hq⟩
    simp only [Prod.map, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    refine ⟨⟨x, rfl⟩, ⟨y, rfl⟩, ?_⟩
    rintro _ _ ⟨⟨u, v⟩, huv, hh⟩
    simp only [Prod.map, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    simp only
    rw [g62h_inner1 chi hchi, g62h_inner1 chi hchi]
    exact h u v huv

theorem solution {n : ℕ} (hn : 0 < n)
    (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1)
    (a : ConfigurationL2 n →ₗ.[ℂ] ConfigurationL2 n) :
    (∀ (lambda : ℂ) (Psi : windowSpace chi),
      ((Psi : PhaseL2 n), lambda • (Psi : PhaseL2 n)) ∈
        transportGraph chi (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n)) ↔
      ∃ psi : ConfigurationL2 n,
        tensorEmbedding chi psi = (Psi : PhaseL2 n) ∧ (psi, lambda • psi) ∈ a.graph) ∧
    graphSpectrumOn (windowSpace chi) (transportGraph chi (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n))) =
      graphSpectrumOn (⊤ : Submodule ℂ (ConfigurationL2 n)) (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n)) := by
  set T := tensorEmbedding chi with hTdef
  have hinj := g62h_inj chi hchi
  constructor
  · intro lam Psi
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      simp only at hu hv
      refine ⟨u, hu, ?_⟩
      have : v = lam • u := hinj (by rw [hv, map_smul, hu])
      rw [← this]; exact huv
    · rintro ⟨psi, hpsi, hG⟩
      exact ⟨psi, lam • psi, hG, hpsi, by show T (lam • psi) = _; rw [map_smul, hpsi]⟩
  · generalize (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n)) = G
    let E : (⊤ : Submodule ℂ (ConfigurationL2 n)) ≃ₗᵢ[ℂ] windowSpace chi :=
      (LinearIsometryEquiv.ofTop _ (⊤ : Submodule ℂ (ConfigurationL2 n)) rfl).trans (g62h_U chi hchi)
    have hE : ∀ f, (E f : PhaseL2 n) = T (f : ConfigurationL2 n) := fun f => rfl
    have hEs : ∀ u : ConfigurationL2 n, E.symm ⟨T u, ⟨u, rfl⟩⟩ = ⟨u, trivial⟩ := by
      intro u
      apply E.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [hE]
    ext lam
    simp only [graphSpectrumOn, Set.mem_setOf_eq]
    rw [not_iff_not]
    constructor
    · rintro ⟨B, h1, h2⟩
      let Ec := E.toContinuousLinearEquiv
      refine ⟨(Ec.symm : windowSpace chi →L[ℂ] _).comp (B.comp (Ec : _ →L[ℂ] windowSpace chi)), ?_, ?_⟩
      · intro f
        obtain ⟨u, v, huv, hu, hv⟩ := h1 (E f)
        simp only at hu hv
        have hBf : B (E f) = ⟨T u, ⟨u, rfl⟩⟩ := Subtype.ext hu.symm
        have hcomp : (Ec.symm : windowSpace chi →L[ℂ] _).comp (B.comp (Ec : _ →L[ℂ] windowSpace chi)) f
            = E.symm (B (E f)) := rfl
        rw [hcomp, hBf, hEs]
        have hv' : v = lam • u + (f : ConfigurationL2 n) :=
          hinj (by rw [hv, map_add, map_smul, ← hE f, hu])
        simp only
        rw [← hv']; exact huv
      · intro x y hxy
        have hmem : (((E x : windowSpace chi) : PhaseL2 n), ((E y : windowSpace chi) : PhaseL2 n)) ∈
            transportGraph chi G := ⟨x, y, hxy, (hE x).symm, (hE y).symm⟩
        have := h2 (E x) (E y) hmem
        show E.symm (B (E (y - lam • x))) = x
        rw [map_sub, map_smul, this, LinearIsometryEquiv.symm_apply_apply]
    · rintro ⟨B, h1, h2⟩
      let Ec := E.toContinuousLinearEquiv
      refine ⟨(Ec : _ →L[ℂ] windowSpace chi).comp (B.comp (Ec.symm : windowSpace chi →L[ℂ] _)), ?_, ?_⟩
      · intro F
        have hcomp : (Ec : _ →L[ℂ] windowSpace chi).comp (B.comp (Ec.symm : windowSpace chi →L[ℂ] _)) F
            = E (B (E.symm F)) := rfl
        rw [hcomp]
        refine ⟨_, _, h1 (E.symm F), rfl, ?_⟩
        simp only
        rw [map_add, map_smul, ← hE, ← hE, LinearIsometryEquiv.apply_symm_apply]
      · intro x y hxy
        obtain ⟨u, v, huv, hu, hv⟩ := hxy
        simp only at hu hv
        have hx : E.symm x = ⟨u, trivial⟩ := by
          have : x = ⟨T u, ⟨u, rfl⟩⟩ := Subtype.ext hu.symm
          rw [this, hEs]
        have hy : E.symm y = ⟨v, trivial⟩ := by
          have : y = ⟨T v, ⟨v, rfl⟩⟩ := Subtype.ext hv.symm
          rw [this, hEs]
        have := h2 ⟨u, trivial⟩ ⟨v, trivial⟩ huv
        show E (B (E.symm (y - lam • x))) = x
        rw [map_sub, map_smul, hx, hy, this, ← hx, LinearIsometryEquiv.apply_symm_apply]
