-- Prove2me | solution 1 for ProjLikeRetr.Retractor.retractor_gives_retraction
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T00:06:49.856978+00:00
-- url     : https://prove2.me/submissions/e08d162c-60c1-4167-9586-093441627bdd

-- Licensed under Apache 2.0. Full exact theorem: retractors give retractions.
import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ProjLikeRetr_Retractor_IsRetraction
import Definitions.Def_ProjLikeRetr_Retractor_IsRetractor
import Definitions.Def_ProjLikeRetr_Retractor_retractorR

open Filter Topology


noncomputable section
open Set
open scoped Topology
namespace RetractorProof

def coordinateSlice (N d : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin N)) where
  carrier := {v | ∀ i : Fin N, d ≤ i.val → v i = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv i hi; simp [hu i hi, hv i hi]
  smul_mem' := by intro c u hu i hi; simp [hu i hi]

def sliceEquiv {N d : ℕ} (hd : d ≤ N) :
    coordinateSlice N d ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun x := WithLp.toLp 2 (fun i => (x : EuclideanSpace ℝ (Fin N)) (Fin.castLE hd i))
  invFun y := ⟨WithLp.toLp 2 (fun i : Fin N => if hi : i.val < d then y ⟨i.val,hi⟩ else 0), by
    intro i hi
    simp [not_lt.mpr hi]⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    change (if hi : i.val < d then x.val (Fin.castLE hd ⟨i.val,hi⟩) else 0) = x.val i
    split_ifs with hi
    · rfl
    · exact (x.property i (Nat.le_of_not_lt hi)).symm
  right_inv y := by
    ext i
    change (if hi : (Fin.castLE hd i).val < d then y ⟨(Fin.castLE hd i).val,hi⟩ else 0) = y i
    simp
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl

theorem finrank_coordinateSlice {N d : ℕ} (hd : d ≤ N) :
    Module.finrank ℝ (coordinateSlice N d) = d := by
  rw [(sliceEquiv hd).finrank_eq]
  exact finrank_euclideanSpace_fin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def sliceParam (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (a : E) (d : ℕ) (s : coordinateSlice (Module.finrank ℝ E) d) : E :=
  φ.symm (φ a + (s : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))

def sliceCoord (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (a : E) (d : ℕ) (x : E) : coordinateSlice (Module.finrank ℝ E) d :=
  (coordinateSlice (Module.finrank ℝ E) d).orthogonalProjectionOnto (φ x - φ a)

omit [FiniteDimensional ℝ E] in
theorem sliceParam_zero (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    {a : E} (ha : a ∈ φ.source) (d : ℕ) : sliceParam φ a d 0 = a := by
  simp [sliceParam, φ.left_inv ha]

omit [FiniteDimensional ℝ E] in
theorem sliceCoord_self (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (a : E) (d : ℕ) : sliceCoord φ a d a = 0 := by simp [sliceCoord]

end RetractorProof


noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
variable (a : E) (d : ℕ)

def paramDomain : Set (coordinateSlice (Module.finrank ℝ E) d) :=
  {s | φ a + (s : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∈ φ.target}

omit [FiniteDimensional ℝ E] in
theorem paramDomain_open : IsOpen (paramDomain φ a d) :=
  φ.open_target.preimage (continuous_const.add continuous_subtype_val)

omit [FiniteDimensional ℝ E] in
theorem zero_mem_paramDomain (ha : a ∈ φ.source) : 0 ∈ paramDomain φ a d := by
  simpa [paramDomain] using φ.map_source ha

omit [FiniteDimensional ℝ E] in
theorem param_mem_source {s : coordinateSlice (Module.finrank ℝ E) d}
    (hs : s ∈ paramDomain φ a d) : sliceParam φ a d s ∈ φ.source :=
  φ.map_target hs

omit [FiniteDimensional ℝ E] in
theorem chart_param {s : coordinateSlice (Module.finrank ℝ E) d}
    (hs : s ∈ paramDomain φ a d) :
    φ (sliceParam φ a d s) = φ a + (s : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  φ.right_inv hs

omit [FiniteDimensional ℝ E] in
theorem sliceParam_contDiffAt {k : ℕ} {s : coordinateSlice (Module.finrank ℝ E) d}
    (hs : s ∈ paramDomain φ a d) (hψ : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target) :
    ContDiffAt ℝ (k : WithTop ℕ∞) (sliceParam φ a d) s := by
  have hc : ContDiffAt ℝ (k : WithTop ℕ∞)
      (fun u : coordinateSlice (Module.finrank ℝ E) d => φ a + (u : _)) s :=
    contDiffAt_const.add (coordinateSlice (Module.finrank ℝ E) d).subtypeL.contDiff.contDiffAt
  exact (hψ.contDiffAt (φ.open_target.mem_nhds hs)).comp s hc

omit [FiniteDimensional ℝ E] in
theorem sliceParam_contDiffOn {k : ℕ}
    (hψ : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target) :
    ContDiffOn ℝ (k : WithTop ℕ∞) (sliceParam φ a d) (paramDomain φ a d) :=
  fun _ hs => (sliceParam_contDiffAt φ a d hs hψ).contDiffWithinAt

omit [FiniteDimensional ℝ E] in
theorem chart_derivative_left_inverse {k : ℕ} (hk : 1 ≤ k) {x : E}
    (hx : x ∈ φ.source) (hφ : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (hψ : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target) :
    (fderiv ℝ φ.symm (φ x)).comp (fderiv ℝ φ x) = ContinuousLinearMap.id ℝ E := by
  have hf := (hφ.contDiffAt (φ.open_source.mem_nhds hx)).differentiableAt (by simpa using (show k ≠ 0 by omega))
  have hg := (hψ.contDiffAt (φ.open_target.mem_nhds (φ.map_source hx))).differentiableAt (by simpa using (show k ≠ 0 by omega))
  have hh := hg.hasFDerivAt.comp x hf.hasFDerivAt
  have heq : (φ.symm ∘ φ) =ᶠ[𝓝 x] id := φ.eventually_left_inverse hx
  have he := hh.congr_of_eventuallyEq heq.symm
  exact he.unique (hasFDerivAt_id x)

omit [FiniteDimensional ℝ E] in
theorem chart_param_derivative {k : ℕ} (hk : 1 ≤ k)
    {s : coordinateSlice (Module.finrank ℝ E) d} (hs : s ∈ paramDomain φ a d)
    (hφ : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (hψ : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target) :
    (fderiv ℝ φ (sliceParam φ a d s)).comp (fderiv ℝ (sliceParam φ a d) s) =
      (coordinateSlice (Module.finrank ℝ E) d).subtypeL := by
  have hg := (sliceParam_contDiffAt φ a d hs hψ).differentiableAt (by simpa using (show k ≠ 0 by omega))
  have hf := (hφ.contDiffAt (φ.open_source.mem_nhds (param_mem_source φ a d hs))).differentiableAt (by simpa using (show k ≠ 0 by omega))
  have hc := hf.hasFDerivAt.comp s hg.hasFDerivAt
  have heq : (φ ∘ sliceParam φ a d) =ᶠ[𝓝 s]
      (fun u : coordinateSlice (Module.finrank ℝ E) d => φ a + (u : _)) := by
    filter_upwards [(paramDomain_open φ a d).mem_nhds hs] with u hu
    exact chart_param φ a d hu
  have he := hc.congr_of_eventuallyEq heq.symm
  exact he.unique ((coordinateSlice (Module.finrank ℝ E) d).subtypeL.hasFDerivAt.const_add (φ a))

omit [FiniteDimensional ℝ E] in
theorem param_derivative_injective {k : ℕ} (hk : 1 ≤ k)
    {s : coordinateSlice (Module.finrank ℝ E) d} (hs : s ∈ paramDomain φ a d)
    (hφ : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (hψ : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target) :
    Function.Injective (fderiv ℝ (sliceParam φ a d) s) := by
  intro u v huv
  have hi := chart_param_derivative φ a d hk hs hφ hψ
  have he := congrArg (fderiv ℝ φ (sliceParam φ a d s)) huv
  have hu := congrArg (fun L : coordinateSlice (Module.finrank ℝ E) d →L[ℝ]
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => L u) hi
  have hv := congrArg (fun L : coordinateSlice (Module.finrank ℝ E) d →L[ℝ]
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => L v) hi
  exact Subtype.ext (hu.symm.trans (he.trans hv))

end RetractorProof


noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
open ProjLikeRetr.Retractor

variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem derivative_identity_on_tangent {M U : Set E} {x : E}
    {f : E → E} {L : E →L[ℝ] E} (hU : U ∈ 𝓝 x) (hx : x ∈ M)
    (hf : HasFDerivAt f L x) (he : EqOn f id (M ∩ U)) :
    ∀ v ∈ tangentSpace M x, L v = v := by
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hz : HasFDerivWithinAt f (ContinuousLinearMap.id ℝ E) (M ∩ U) x :=
    (hasFDerivAt_id x).hasFDerivWithinAt.congr' he ⟨hx, hxU⟩
  have hu := hf.hasFDerivWithinAt.unique_on hz
  rw [tangentConeAt_inter_nhds hU] at hu
  have hle : tangentSpace M x ≤ LinearMap.ker (L - ContinuousLinearMap.id ℝ E).toLinearMap := by
    apply Submodule.span_le.mpr
    intro v hv
    change L v - v = 0
    exact sub_eq_zero.mpr (hu hv)
  intro v hv
  exact sub_eq_zero.mp (hle hv)

theorem param_range_le_tangent {M : Set E} {V : Set S} {g : S → E} {q : S}
    {G : S →L[ℝ] E} (hV : V ∈ 𝓝 q) (hg : HasFDerivAt g G q)
    (hM : MapsTo g V M) : LinearMap.range G.toLinearMap ≤ tangentSpace M (g q) := by
  rintro v ⟨w, rfl⟩
  apply Submodule.subset_span
  apply tangentConeAt_mono (image_subset_iff.mpr hM)
  apply hg.hasFDerivWithinAt.mapsTo_tangent_cone
  rw [tangentConeAt_of_mem_nhds hV]
  trivial

theorem tangent_eq_param_range {M U : Set E} {V : Set S} {g : S → E} {f : E → S}
    {x : E} {G : S →L[ℝ] E} {F : E →L[ℝ] S}
    (hU : U ∈ 𝓝 x) (hx : x ∈ M) (hV : V ∈ 𝓝 (f x))
    (hg : HasFDerivAt g G (f x)) (hf : HasFDerivAt f F x)
    (hinv : EqOn (g ∘ f) id (M ∩ U)) (hM : MapsTo g V M) :
    tangentSpace M x = LinearMap.range G.toLinearMap := by
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have he : g (f x) = x := hinv ⟨hx, hxU⟩
  apply le_antisymm
  · intro v hv
    exact ⟨F v, derivative_identity_on_tangent hU hx (hg.comp x hf) hinv v hv⟩
  · simpa [he] using param_range_le_tangent hV hg hM


theorem derivative_left_inverse {V : Set S} {g : S → E} {f : E → S} {q : S}
    {G : S →L[ℝ] E} {F : E →L[ℝ] S} (hV : V ∈ 𝓝 q)
    (hg : HasFDerivAt g G q) (hf : HasFDerivAt f F (g q))
    (hinv : EqOn (f ∘ g) id V) : F.comp G = ContinuousLinearMap.id ℝ S := by
  have he : (f ∘ g) =ᶠ[𝓝 q] id := Filter.Eventually.mono hV (fun _ hv => hinv hv)
  exact ((hf.comp q hg).congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id q)

end RetractorProof


noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
variable (a : E) (d : ℕ) (M : Set E)

omit [FiniteDimensional ℝ E] in
theorem param_mem_manifold (ha : a ∈ M ∩ φ.source)
    (hM : M ∩ φ.source = {x | x ∈ φ.source ∧ ∀ i, d ≤ i.val → φ x i = 0})
    {s : coordinateSlice (Module.finrank ℝ E) d} (hs : s ∈ paramDomain φ a d) :
    sliceParam φ a d s ∈ M ∩ φ.source := by
  have hb := (Set.ext_iff.mp hM a).mp ha
  rw [hM]
  refine ⟨param_mem_source φ a d hs, ?_⟩
  intro i hi
  rw [chart_param φ a d hs]
  simp [hb.2 i hi, s.property i hi]

omit [FiniteDimensional ℝ E] in
theorem coord_param {s : coordinateSlice (Module.finrank ℝ E) d}
    (hs : s ∈ paramDomain φ a d) : sliceCoord φ a d (sliceParam φ a d s) = s := by
  simp [sliceCoord, chart_param φ a d hs]

omit [FiniteDimensional ℝ E] in
theorem chart_difference_mem (ha : a ∈ M ∩ φ.source)
    (hM : M ∩ φ.source = {x | x ∈ φ.source ∧ ∀ i, d ≤ i.val → φ x i = 0})
    {x : E} (hx : x ∈ M ∩ φ.source) :
    φ x - φ a ∈ coordinateSlice (Module.finrank ℝ E) d := by
  have hb := (Set.ext_iff.mp hM a).mp ha
  have hc := (Set.ext_iff.mp hM x).mp hx
  intro i hi
  simp [hc.2 i hi, hb.2 i hi]

omit [FiniteDimensional ℝ E] in
theorem coe_coord (ha : a ∈ M ∩ φ.source)
    (hM : M ∩ φ.source = {x | x ∈ φ.source ∧ ∀ i, d ≤ i.val → φ x i = 0})
    {x : E} (hx : x ∈ M ∩ φ.source) :
    (sliceCoord φ a d x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = φ x - φ a := by
  exact (coordinateSlice (Module.finrank ℝ E) d).starProjection_eq_self_iff.mpr
    (chart_difference_mem φ a d M ha hM hx)

omit [FiniteDimensional ℝ E] in
theorem coord_mem_domain (ha : a ∈ M ∩ φ.source)
    (hM : M ∩ φ.source = {x | x ∈ φ.source ∧ ∀ i, d ≤ i.val → φ x i = 0})
    {x : E} (hx : x ∈ M ∩ φ.source) : sliceCoord φ a d x ∈ paramDomain φ a d := by
  change φ a + (sliceCoord φ a d x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∈ φ.target
  rw [coe_coord φ a d M ha hM hx]
  have he : φ a + (φ x - φ a) = φ x := by abel
  rw [he]
  exact φ.map_source hx.2

omit [FiniteDimensional ℝ E] in
theorem param_coord (ha : a ∈ M ∩ φ.source)
    (hM : M ∩ φ.source = {x | x ∈ φ.source ∧ ∀ i, d ≤ i.val → φ x i = 0})
    {x : E} (hx : x ∈ M ∩ φ.source) : sliceParam φ a d (sliceCoord φ a d x) = x := by
  unfold sliceParam
  rw [coe_coord φ a d M ha hM hx]
  have he : φ a + (φ x - φ a) = φ x := by abel
  rw [he]
  exact φ.left_inv hx.2

omit [FiniteDimensional ℝ E] in
theorem sliceCoord_contDiffAt {k : ℕ} {x : E} (hx : x ∈ φ.source)
    (hφ : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source) :
    ContDiffAt ℝ (k : WithTop ℕ∞) (sliceCoord φ a d) x := by
  exact (coordinateSlice (Module.finrank ℝ E) d).orthogonalProjectionOnto.contDiff.contDiffAt.comp x
    ((hφ.contDiffAt (φ.open_source.mem_nhds hx)).sub contDiffAt_const)

end RetractorProof


noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
open ProjLikeRetr.Retractor

structure LocalGeometry {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup S] [NormedSpace ℝ S] (k d : ℕ) (M : Set E) (a : E) where
  g : S → E
  f : E → S
  U : Set E
  V : Set S
  open_U : IsOpen U
  open_V : IsOpen V
  mem_U : a ∈ U
  mem_V : (0 : S) ∈ V
  smooth_g : ContDiffOn ℝ (k : WithTop ℕ∞) g V
  smooth_f : ContDiffOn ℝ (k : WithTop ℕ∞) f U
  g_zero : g 0 = a
  f_base : f a = 0
  g_mem : ∀ q ∈ V, g q ∈ M ∩ U
  f_mem : ∀ x ∈ M ∩ U, f x ∈ V
  fg : ∀ q ∈ V, f (g q) = q
  gf : ∀ x ∈ M ∩ U, g (f x) = x
  tangent : ∀ q ∈ V, tangentSpace M (g q) = LinearMap.range (fderiv ℝ g q).toLinearMap
  injective : ∀ q ∈ V, Function.Injective (fderiv ℝ g q)
  derivative_fg : ∀ q ∈ V,
    (fderiv ℝ f (g q)).comp (fderiv ℝ g q) = ContinuousLinearMap.id ℝ S
  derivative_gf : ∀ x ∈ M ∩ U, ∀ u ∈ tangentSpace M x,
    fderiv ℝ g (f x) (fderiv ℝ f x u) = u
  dimension : Module.finrank ℝ S = d


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem localGeometry_exists {k d : ℕ} {M : Set E} {a : E}
    (hk : 1 ≤ k) (hM : IsSubmanifoldAt k d M a) :
    Nonempty (LocalGeometry (S := coordinateSlice (Module.finrank ℝ E) d) k d M a) := by
  rcases hM with ⟨hd, haM, φ, ha, hφ, hψ, hslice⟩
  let g := sliceParam φ a d
  let f := sliceCoord φ a d
  let V := paramDomain φ a d
  have hgm : ∀ q ∈ V, g q ∈ M ∩ φ.source :=
    fun q hq => param_mem_manifold φ a d M ⟨haM, ha⟩ hslice hq
  have hfm : ∀ x ∈ M ∩ φ.source, f x ∈ V :=
    fun x hx => coord_mem_domain φ a d M ⟨haM, ha⟩ hslice hx
  have hfg : ∀ q ∈ V, f (g q) = q := fun q hq => coord_param φ a d hq
  have hgf : ∀ x ∈ M ∩ φ.source, g (f x) = x :=
    fun x hx => param_coord φ a d M ⟨haM, ha⟩ hslice hx
  have hg : ∀ q ∈ V, HasFDerivAt g (fderiv ℝ g q) q := by
    intro q hq
    exact ((sliceParam_contDiffAt φ a d hq hψ).differentiableAt
      (by simpa using (show k ≠ 0 by omega))).hasFDerivAt
  have hf : ∀ x ∈ φ.source, HasFDerivAt f (fderiv ℝ f x) x := by
    intro x hx
    exact ((sliceCoord_contDiffAt φ a d hx hφ).differentiableAt
      (by simpa using (show k ≠ 0 by omega))).hasFDerivAt
  have hderfg : ∀ q ∈ V, (fderiv ℝ f (g q)).comp (fderiv ℝ g q) =
      ContinuousLinearMap.id ℝ (coordinateSlice (Module.finrank ℝ E) d) := by
    intro q hq
    exact derivative_left_inverse ((paramDomain_open φ a d).mem_nhds hq)
      (hg q hq) (hf (g q) (hgm q hq).2) (fun q hq => hfg q hq)
  refine ⟨{
    g := g
    f := f
    U := φ.source
    V := V
    open_U := φ.open_source
    open_V := paramDomain_open φ a d
    mem_U := ha
    mem_V := zero_mem_paramDomain φ a d ha
    smooth_g := sliceParam_contDiffOn φ a d hψ
    smooth_f := fun x hx => (sliceCoord_contDiffAt φ a d hx hφ).contDiffWithinAt
    g_zero := sliceParam_zero φ ha d
    f_base := sliceCoord_self φ a d
    g_mem := hgm
    f_mem := hfm
    fg := hfg
    gf := hgf
    tangent := ?_
    injective := ?_
    derivative_fg := hderfg
    derivative_gf := ?_
    dimension := finrank_coordinateSlice hd }⟩
  · intro q hq
    have hh := tangent_eq_param_range (φ.open_source.mem_nhds (hgm q hq).2)
      (hgm q hq).1 ((paramDomain_open φ a d).mem_nhds (hfm (g q) (hgm q hq)))
      (hg (f (g q)) (hfm (g q) (hgm q hq))) (hf (g q) (hgm q hq).2)
      (fun x hx => hgf x hx) (fun q hq => (hgm q hq).1)
    simpa [hfg q hq] using hh
  · intro q hq u v huv
    have hu := congrArg (fun L => L u) (hderfg q hq)
    have hv := congrArg (fun L => L v) (hderfg q hq)
    exact hu.symm.trans ((congrArg (fderiv ℝ f (g q)) huv).trans hv)
  · intro x hx u hu
    exact derivative_identity_on_tangent (φ.open_source.mem_nhds hx.2) hx.1
      ((hg (f x) (hfm x hx)).comp x (hf x hx.2)) (fun x hx => hgf x hx) u hu

end RetractorProof


noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
open ProjLikeRetr.Retractor
variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
  {k d : ℕ} {M : Set E} {a : E}

omit [FiniteDimensional ℝ S] in
theorem LocalGeometry.tangent_dimension (G : LocalGeometry (S := S) k d M a)
    {q : S} (hq : q ∈ G.V) : Module.finrank ℝ (tangentSpace M (G.g q)) = d := by
  rw [G.tangent q hq, LinearMap.finrank_range_of_inj (G.injective q hq), G.dimension]


end RetractorProof


noncomputable section
open scoped Topology
namespace RetractorProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma projector_lower_bound (D₀ D : Submodule ℝ E)
    (hclose : ‖D.starProjection - D₀.starProjection‖ < (1 / 2 : ℝ)) (w : D₀) :
    ‖(w : E)‖ ≤ 2 * ‖D.starProjection w‖ := by
  have hdiff : ‖D.starProjection (w : E) - (w : E)‖ ≤ (1 / 2 : ℝ) * ‖(w : E)‖ := by
    calc
      _ = ‖(D.starProjection - D₀.starProjection) (w : E)‖ := by simp
      _ ≤ ‖D.starProjection - D₀.starProjection‖ * ‖(w : E)‖ :=
        (D.starProjection - D₀.starProjection).le_opNorm _
      _ ≤ (1 / 2 : ℝ) * ‖(w : E)‖ := mul_le_mul_of_nonneg_right hclose.le (norm_nonneg _)
  have ht := norm_sub_le (D.starProjection (w : E)) (D.starProjection (w : E) - (w : E))
  have he : D.starProjection (w : E) - (D.starProjection (w : E) - (w : E)) = (w : E) := by abel
  rw [he] at ht
  linarith

lemma projector_coordinates (D₀ D : Submodule ℝ E)
    (hdim : Module.finrank ℝ D₀ = Module.finrank ℝ D)
    (hclose : ‖D.starProjection - D₀.starProjection‖ < (1 / 2 : ℝ))
    {c : E} (hc : c ∈ D) :
    ∃ w : D₀, D.starProjection (w : E) = c ∧ ‖w‖ ≤ 2 * ‖c‖ := by
  let L : D₀ →ₗ[ℝ] D :=
    (D.starProjection.toLinearMap.comp D₀.subtype).codRestrict D
      (fun w => D.starProjection_apply_mem w)
  have hinj : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro w hw
    have hz : D.starProjection (w : E) = 0 := congrArg Subtype.val hw
    have hn := projector_lower_bound D₀ D hclose w
    rw [hz, norm_zero, mul_zero] at hn
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨w, hw⟩ := hsurj ⟨c, hc⟩
  have he : D.starProjection (w : E) = c := congrArg Subtype.val hw
  refine ⟨w, he, ?_⟩
  simpa [he] using projector_lower_bound D₀ D hclose w

end RetractorProof


noncomputable section
namespace RetractorProof
variable {E S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

lemma transverse_difference_invertible (B : S →L[ℝ] E) (D : Submodule ℝ E)
    (hB : Function.Injective B)
    (hdis : D ⊓ B.toLinearMap.range = ⊥)
    (hdim : Module.finrank ℝ S + Module.finrank ℝ D = Module.finrank ℝ E) :
    ((B.comp (ContinuousLinearMap.fst ℝ S D)) -
      D.subtypeL.comp (ContinuousLinearMap.snd ℝ S D)).IsInvertible := by
  let L : S × D →L[ℝ] E := B.comp (ContinuousLinearMap.fst ℝ S D) -
    D.subtypeL.comp (ContinuousLinearMap.snd ℝ S D)
  have hinj : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    rintro ⟨s, w⟩ hw
    have he : B s = (w : E) := sub_eq_zero.mp hw
    have hm : (w : E) ∈ D ⊓ B.toLinearMap.range := ⟨w.property, ⟨s, he⟩⟩
    rw [hdis] at hm
    have hw0 : w = 0 := Subtype.ext (by simpa using hm)
    have hs0 : s = 0 := hB (by simpa [hw0] using he)
    exact Prod.ext hs0 hw0
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa only [Module.finrank_prod] using hdim)).mp hinj
  refine ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ?_⟩
  rfl

end RetractorProof


noncomputable section
open Filter
open scoped Topology
namespace RetractorProof

variable {P W E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma local_implicit_branch {m : ℕ} (hm : m ≠ 0) (F : P × W → E)
    (hF : ContDiffAt ℝ m F (0, 0)) (hzero : F (0, 0) = 0)
    (hinv : (fderiv ℝ F (0, 0) ∘L ContinuousLinearMap.inr ℝ P W).IsInvertible) :
    ∃ b : P → W, b 0 = 0 ∧ ContDiffAt ℝ m b 0 ∧
      (∀ᶠ p in 𝓝 (0 : P), F (p, b p) = 0) ∧
      (∀ᶠ v in 𝓝 ((0, 0) : P × W), F v = 0 ↔ b v.1 = v.2) := by
  have hm' : (m : WithTop ℕ∞) ≠ 0 := by exact_mod_cast hm
  refine ⟨hF.implicitFunction hm' hinv, hF.implicitFunction_apply_self hm' hinv,
    hF.contDiffAt_implicitFunction hm' hinv, ?_, ?_⟩
  · simpa [hzero] using hF.eventually_apply_implicitFunction hm' hinv
  · simpa [hzero] using hF.eventually_apply_eq_iff_implicitFunction hm' hinv

end RetractorProof


noncomputable section
namespace RetractorProof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def tangentLift (f : E → F) (p : E × E) : F × F :=
  (f p.1, (fderiv ℝ f p.1) p.2)

lemma tangentLift_zero (f : E → F) (x : E) : tangentLift f (x, 0) = (f x, 0) := by
  simp [tangentLift]

lemma tangentLift_contDiffAt {f : E → F} {k : ℕ} (hk : 1 ≤ k) {p : E × E}
    (hf : ContDiffAt ℝ (k : WithTop ℕ∞) f p.1) :
    ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (tangentLift f) p := by
  have hle : ((k - 1 : ℕ) : WithTop ℕ∞) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hs : ((k - 1 : ℕ) : WithTop ℕ∞) + 1 ≤ k := by
    exact_mod_cast (show k - 1 + 1 ≤ k by omega)
  exact ((hf.of_le hle).comp p contDiffAt_fst).prodMk
    (((hf.fderiv_right hs).comp p contDiffAt_fst).clm_apply contDiffAt_snd)

end RetractorProof


noncomputable section
open Filter
open scoped Topology
namespace RetractorProof
variable {S W E : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def retractorEquation (g : S → E) (Q : S × S → W →L[ℝ] E)
    (v : (S × S) × (S × W)) : E :=
  g v.2.1 - g v.1.1 - (fderiv ℝ g v.1.1) v.1.2 - Q v.1 v.2.2

omit [CompleteSpace S] [CompleteSpace W] [CompleteSpace E] in
lemma retractorEquation_smooth {g : S → E} {Q : S × S → W →L[ℝ] E}
    {k : ℕ} (hk : 2 ≤ k) (hg : ContDiffAt ℝ (k : WithTop ℕ∞) g 0)
    (hQ : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) Q (0, 0)) :
    ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (retractorEquation g Q) ((0, 0), (0, 0)) := by
  have hle : ((k - 1 : ℕ) : WithTop ℕ∞) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hg' := hg.of_le hle
  have hLift := tangentLift_contDiffAt (show 1 ≤ k by omega) (p := ((0, 0) : S × S)) hg
  have ht : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun v : (S × S) × (S × W) => g v.2.1) ((0, 0), (0, 0)) :=
    hg'.comp ((0, 0), (0, 0)) (contDiffAt_fst.comp _ contDiffAt_snd)
  have hq : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun v : (S × S) × (S × W) => g v.1.1) ((0, 0), (0, 0)) :=
    hg'.comp ((0, 0), (0, 0)) (contDiffAt_fst.comp _ contDiffAt_fst)
  have hb : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun v : (S × S) × (S × W) => (fderiv ℝ g v.1.1) v.1.2) ((0, 0), (0, 0)) :=
    (contDiffAt_snd.comp ((0, 0) : S × S) hLift).comp
      (((0, 0), (0, 0)) : (S × S) × (S × W)) contDiffAt_fst
  have hw : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun v : (S × S) × (S × W) => Q v.1 v.2.2) ((0, 0), (0, 0)) :=
    (hQ.comp (((0, 0), (0, 0)) : (S × S) × (S × W)) contDiffAt_fst).clm_apply
      (contDiffAt_snd.comp (((0, 0), (0, 0)) : (S × S) × (S × W)) contDiffAt_snd)
  exact ((ht.sub hq).sub hb).sub hw

omit [CompleteSpace S] [CompleteSpace W] [CompleteSpace E] in
lemma retractorEquation_partial {g : S → E} {Q : S × S → W →L[ℝ] E}
    (hg : DifferentiableAt ℝ g 0) :
    HasFDerivAt (fun v : S × W => retractorEquation g Q ((0, 0), v))
      ((fderiv ℝ g 0).comp (ContinuousLinearMap.fst ℝ S W) -
        (Q (0, 0)).comp (ContinuousLinearMap.snd ℝ S W)) (0, 0) := by
  have hfst : HasFDerivAt (fun v : S × W => v.1)
      (ContinuousLinearMap.fst ℝ S W) (0, 0) := hasFDerivAt_fst
  have hd : HasFDerivAt (fun v : S × W => g v.1)
      ((fderiv ℝ g 0).comp (ContinuousLinearMap.fst ℝ S W)) (0, 0) :=
    hg.hasFDerivAt.comp ((0, 0) : S × W) hfst
  exact ((hd.sub_const (g 0)).sub_const ((fderiv ℝ g 0) 0)).sub
    (((Q (0, 0)).comp (ContinuousLinearMap.snd ℝ S W)).hasFDerivAt)

lemma retractorEquation_branch {g : S → E} {Q : S × S → W →L[ℝ] E}
    {k : ℕ} (hk : 2 ≤ k) (hg : ContDiffAt ℝ (k : WithTop ℕ∞) g 0)
    (hQ : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) Q (0, 0))
    (hinv : ((fderiv ℝ g 0).comp (ContinuousLinearMap.fst ℝ S W) -
      (Q (0, 0)).comp (ContinuousLinearMap.snd ℝ S W)).IsInvertible) :
    ∃ b : S × S → S × W, b (0, 0) = (0, 0) ∧
      ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) b (0, 0) ∧
      (∀ᶠ p in 𝓝 ((0, 0) : S × S), retractorEquation g Q (p, b p) = 0) ∧
      (∀ᶠ v in 𝓝 (((0, 0), (0, 0)) : (S × S) × (S × W)),
        retractorEquation g Q v = 0 ↔ b v.1 = v.2) := by
  have hF := retractorEquation_smooth hk hg hQ
  have hm : (k - 1 : ℕ) ≠ 0 := by omega
  have hm' : ((k - 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast hm
  have hg' := hg.differentiableAt (by exact_mod_cast (show k ≠ 0 by omega))
  have hp := retractorEquation_partial (Q := Q) hg'
  have hc := hF.differentiableAt hm' |>.hasFDerivAt.comp ((0, 0) : S × W)
    (ContinuousLinearMap.inr ℝ (S × S) (S × W)).hasFDerivAt
  have he := hp.unique hc
  have hi : (fderiv ℝ (retractorEquation g Q) ((0, 0), (0, 0)) ∘L
      ContinuousLinearMap.inr ℝ (S × S) (S × W)).IsInvertible := by rw [← he]; exact hinv
  exact local_implicit_branch hm _ hF (by simp [retractorEquation]) hi

end RetractorProof


noncomputable section
open Filter
open scoped Topology
namespace RetractorProof
open RandomGradFree.Nonsmooth

variable {E S W : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
  [NormedAddCommGroup W]

lemma metric_projection_singleton_of_no_closer (M : Set E) (c z : E)
    (hz : z ∈ M) (hunique : ∀ y ∈ M, ‖y - c‖ ≤ ‖z - c‖ → y = z) :
    {y | IsMetricProjection M c y} = {z} := by
  have hmin : IsMetricProjection M c z := by
    refine ⟨hz, fun y hy => ?_⟩
    by_cases h : ‖y - c‖ ≤ ‖z - c‖
    · rw [hunique y hy h]
    · simpa only [norm_sub_rev] using le_of_lt (lt_of_not_ge h)
  ext y
  constructor
  · intro hy
    exact Set.mem_singleton_iff.mpr (hunique y hy.1 (by
      simpa only [norm_sub_rev] using hy.2 z hz))
  · intro hy
    simpa only [Set.mem_singleton_iff.mp hy, Set.mem_ofPred_eq] using hmin

lemma nearest_from_local_equation (M : Set E) (a c z : E)
    (g : S → E) (coord : E → S) (Q : W → E) (D : Set E)
    (ρ η : ℝ)
    (hchart : ∀ y ∈ M, ‖y - a‖ < ρ → g (coord y) = y ∧ ‖coord y‖ < η)
    (hcorrection : ∀ v ∈ D, ∃ w, Q w = v ∧ ‖w‖ ≤ 2 * ‖v‖)
    (hlocal : ∀ t w, ‖t‖ < η → ‖w‖ < η → g t = c + Q w → g t = z)
    (hz : z ∈ M ∧ z - c ∈ D)
    (hc : ‖c - a‖ < ρ / 2)
    (hzcρ : ‖z - c‖ < ρ / 2) (hzcη : ‖z - c‖ < η / 2) :
    {y | IsMetricProjection (M ∩ {y | y - c ∈ D}) c y} = {z} := by
  apply metric_projection_singleton_of_no_closer _ c z hz
  intro y hy hle
  have hya : ‖y - a‖ < ρ := by
    have ht := norm_sub_le (y - c) (a - c)
    have he : y - c - (a - c) = y - a := by abel
    rw [he, norm_sub_rev a c] at ht
    linarith
  obtain ⟨hgy, hcoord⟩ := hchart y hy.1 hya
  obtain ⟨w, hw, hwnorm⟩ := hcorrection (y - c) hy.2
  have hwsmall : ‖w‖ < η := by linarith
  have he : g (coord y) = c + Q w := by rw [hgy, hw]; abel
  have hz' := hlocal (coord y) w hcoord hwsmall he
  simpa only [hgy] using hz'

end RetractorProof


noncomputable section
open Filter Set Metric
open scoped Topology
namespace RetractorProof
open RandomGradFree.Nonsmooth
variable {P E S W : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedAddCommGroup S] [NormedAddCommGroup W]

lemma eventual_nearest_from_chart {p₀ : P} (M : Set E) (a : E)
    (g : S → E) (f : E → S) (c z : P → E) (Q : P → W → E) (D : P → Set E)
    (η : ℝ) (hη : 0 < η)
    (hf : ContinuousAt f a) (hfa : f a = 0)
    (hchart : ∀ᶠ y in 𝓝 a, y ∈ M → g (f y) = y)
    (hc : Tendsto c (𝓝 p₀) (𝓝 a)) (hz : Tendsto z (𝓝 p₀) (𝓝 a))
    (hfeas : ∀ᶠ p in 𝓝 p₀, z p ∈ M ∧ z p - c p ∈ D p)
    (hcor : ∀ᶠ p in 𝓝 p₀, ∀ v ∈ D p, ∃ w, Q p w = v ∧ ‖w‖ ≤ 2 * ‖v‖)
    (hlocal : ∀ᶠ p in 𝓝 p₀, ∀ t w, ‖t‖ < η → ‖w‖ < η →
      g t = c p + Q p w → g t = z p) :
    ∀ᶠ p in 𝓝 p₀, {y | IsMetricProjection (M ∩ {y | y - c p ∈ D p}) (c p) y} = {z p} := by
  have hfsmall : ∀ᶠ y in 𝓝 a, ‖f y‖ < η := by
    have hh := hf.tendsto.eventually (ball_mem_nhds (f a) hη)
    simpa [mem_ball, hfa, dist_zero_right] using hh
  have hboth : ∀ᶠ y in 𝓝 a, y ∈ M → g (f y) = y ∧ ‖f y‖ < η := by
    filter_upwards [hchart, hfsmall] with y hy hs
    exact fun hym => ⟨hy hym, hs⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hboth
  have hcsmall : ∀ᶠ p in 𝓝 p₀, ‖c p - a‖ < ρ / 2 := by
    simpa [mem_ball, dist_eq_norm] using hc.eventually (ball_mem_nhds a (half_pos hρ))
  have hd : Tendsto (fun p => z p - c p) (𝓝 p₀) (𝓝 (0 : E)) := by
    simpa using hz.sub hc
  have hsmallρ : ∀ᶠ p in 𝓝 p₀, ‖z p - c p‖ < ρ / 2 := by
    simpa [mem_ball, dist_zero_right] using hd.eventually (ball_mem_nhds 0 (half_pos hρ))
  have hsmallη : ∀ᶠ p in 𝓝 p₀, ‖z p - c p‖ < η / 2 := by
    simpa [mem_ball, dist_zero_right] using hd.eventually (ball_mem_nhds 0 (half_pos hη))
  filter_upwards [hfeas, hcor, hlocal, hcsmall, hsmallρ, hsmallη] with p hp hcp hlp hcρ hzρ hzη
  exact nearest_from_local_equation M a (c p) (z p) g f (Q p) (D p) ρ η
    (fun y hy hya => hball (by simpa [mem_ball, dist_eq_norm] using hya) hy)
    hcp hlp hp hcρ hzρ hzη

end RetractorProof


noncomputable section
open Filter Set Metric
open scoped Topology
namespace RetractorProof
variable {P S W E : Type*} [NormedAddCommGroup P] [NormedAddCommGroup S]
  [NormedAddCommGroup W] [NormedAddCommGroup E]

lemma uniform_implicit_uniqueness (F : P × (S × W) → E) (b : P → S × W) (p₀ : P)
    (hiff : ∀ᶠ v in 𝓝 (p₀, ((0, 0) : S × W)), F v = 0 ↔ b v.1 = v.2) :
    ∃ η > 0, ∀ᶠ p in 𝓝 p₀, ∀ t w, ‖t‖ < η → ‖w‖ < η →
      F (p, (t, w)) = 0 → b p = (t, w) := by
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hiff
  refine ⟨η, hη, ?_⟩
  filter_upwards [ball_mem_nhds p₀ hη] with p hp
  intro t w ht hw he
  have hmem : (p, (t, w)) ∈ ball (p₀, ((0, 0) : S × W)) η := by
    simpa only [mem_ball, Prod.dist_eq, dist_zero_right] using
      max_lt (show dist p p₀ < η from hp) (max_lt ht hw)
  exact (hball hmem).mp he

variable [NormedSpace ℝ S] [NormedSpace ℝ W] [NormedSpace ℝ E]

lemma equation_zero_section {g : S → E} {Q : S × S → W →L[ℝ] E}
    {b : S × S → S × W}
    (hiff : ∀ᶠ v in 𝓝 (((0, 0), (0, 0)) : (S × S) × (S × W)),
      retractorEquation g Q v = 0 ↔ b v.1 = v.2) :
    ∀ᶠ q in 𝓝 (0 : S), b (q, 0) = (q, 0) := by
  have hc : Continuous (fun q : S => (((q, 0) : S × S), ((q, 0) : S × W))) := by fun_prop
  have he := hc.continuousAt.tendsto.eventually hiff
  filter_upwards [he] with q hq
  exact hq.mp (by simp [retractorEquation])

lemma equation_identity {g : S → E} {Q : S × S → W →L[ℝ] E}
    {p : S × S} {v : S × W} (h : retractorEquation g Q (p, v) = 0) :
    g v.1 = g p.1 + (fderiv ℝ g p.1) p.2 + Q p v.2 := by
  change g v.1 - g p.1 - (fderiv ℝ g p.1) p.2 - Q p v.2 = 0 at h
  apply sub_eq_zero.mp
  calc
    _ = g v.1 - g p.1 - (fderiv ℝ g p.1) p.2 - Q p v.2 := by abel
    _ = 0 := h

end RetractorProof


noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
open ProjLikeRetr.Retractor
variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  {k d : ℕ} {M : Set E} {a : E}

namespace LocalGeometry
variable (G : LocalGeometry (S := S) k d M a)

lemma lift_mem {p : S × S} (hp : p.1 ∈ G.V) : tangentLift G.g p ∈ tangentBundle M := by
  refine ⟨(G.g_mem p.1 hp).1, ?_⟩
  change (fderiv ℝ G.g p.1) p.2 ∈ tangentSpace M (G.g p.1)
  rw [G.tangent p.1 hp]
  exact ⟨p.2, rfl⟩

lemma lift_coord {p : E × E} (hp : p ∈ tangentBundle M) (hu : p.1 ∈ G.U) :
    tangentLift G.g (tangentLift G.f p) = p := by
  apply Prod.ext
  · exact G.gf p.1 ⟨hp.1, hu⟩
  · exact G.derivative_gf p.1 ⟨hp.1, hu⟩ p.2 hp.2

lemma coord_lift {p : S × S} (hp : p.1 ∈ G.V) :
    tangentLift G.f (tangentLift G.g p) = p := by
  apply Prod.ext
  · exact G.fg p.1 hp
  · exact congrArg (fun L : S →L[ℝ] S => L p.2) (G.derivative_fg p.1 hp)

lemma lift_smooth (hk : 1 ≤ k) {p : S × S} (hp : p.1 ∈ G.V) :
    ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (tangentLift G.g) p :=
  tangentLift_contDiffAt hk (G.smooth_g.contDiffAt (G.open_V.mem_nhds hp))

lemma coord_smooth (hk : 1 ≤ k) {p : E × E} (hp : p.1 ∈ G.U) :
    ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (tangentLift G.f) p :=
  tangentLift_contDiffAt hk (G.smooth_f.contDiffAt (G.open_U.mem_nhds hp))

variable [FiniteDimensional ℝ E]

lemma projector_smooth (hk : 1 ≤ k) (D : E × E → Submodule ℝ E)
    (O : Set (E × E)) (hO : IsOpen O) {p : S × S}
    (hp : p.1 ∈ G.V) (hOp : tangentLift G.g p ∈ O)
    (hs : ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun x => (D x).starProjection) (O ∩ tangentBundle M)) :
    ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun q => (D (tangentLift G.g q)).starProjection) p := by
  have hH := G.lift_smooth hk hp
  have hmem : ∀ᶠ q in 𝓝 p, tangentLift G.g q ∈ O ∩ tangentBundle M := by
    filter_upwards [hH.continuousAt.eventually (hO.mem_nhds hOp),
      continuous_fst.continuousAt.eventually (G.open_V.mem_nhds hp)] with q hqO hqV
    exact ⟨hqO, G.lift_mem hqV⟩
  have hc := (hs _ ⟨hOp, G.lift_mem hp⟩).comp_of_preimage_mem_nhdsWithin p
    hH.contDiffWithinAt (s := Set.univ) (by simpa only [nhdsWithin_univ, Filter.Eventually, Set.preimage] using hmem)
  exact hc.contDiffAt (by simp)

end LocalGeometry
end RetractorProof


noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
open ProjLikeRetr.Retractor
variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] {k d : ℕ} {M : Set E} {a : E}
namespace LocalGeometry
variable (G : LocalGeometry (S := S) k d M a) (D : E × E → Submodule ℝ E)

def correctionMap (p : S × S) : D (a, 0) →L[ℝ] E :=
  (D (tangentLift G.g p)).starProjection.comp (D (a, 0)).subtypeL

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ S] in
lemma lift_base : tangentLift G.g ((0, 0) : S × S) = (a, 0) := by
  simp [tangentLift, G.g_zero]

omit [FiniteDimensional ℝ S] in
lemma correction_base : G.correctionMap D (0, 0) = (D (a, 0)).subtypeL := by
  ext w
  simp [correctionMap, G.lift_base]

omit [FiniteDimensional ℝ S] in
lemma correction_smooth_base (hk : 1 ≤ k) (ha : a ∈ M) (hD : IsRetractor k d M D) :
    ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (G.correctionMap D) (0, 0) := by
  obtain ⟨O, hO, hzO, _, hs, _⟩ := hD
  have hQ := G.projector_smooth hk D O hO (p := ((0, 0) : S × S)) G.mem_V
    (by simpa only [G.lift_base] using hzO a ha) hs
  exact hQ.clm_comp contDiffAt_const

omit [FiniteDimensional ℝ S] in
lemma correction_representation (hk : 1 ≤ k) (ha : a ∈ M) (hD : IsRetractor k d M D) :
    ∀ᶠ p in 𝓝 ((0, 0) : S × S), ∀ v ∈ D (tangentLift G.g p),
      ∃ w : D (a, 0), G.correctionMap D p w = v ∧ ‖w‖ ≤ 2 * ‖v‖ := by
  obtain ⟨O, hO, hzO, hdim, hs, _⟩ := hD
  have hQ := G.projector_smooth hk D O hO (p := ((0, 0) : S × S)) G.mem_V
    (by simpa only [G.lift_base] using hzO a ha) hs
  have hH := G.lift_smooth hk (p := ((0, 0) : S × S)) G.mem_V
  have hclose : ∀ᶠ p in 𝓝 ((0, 0) : S × S),
      ‖(D (tangentLift G.g p)).starProjection - (D (a, 0)).starProjection‖ < (1 / 2 : ℝ) := by
    have h := hQ.continuousAt.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))
    simpa only [Metric.mem_ball, dist_eq_norm, G.lift_base] using h
  have hparam : ∀ᶠ p in 𝓝 ((0, 0) : S × S), tangentLift G.g p ∈ O ∩ tangentBundle M := by
    filter_upwards [hH.continuousAt.eventually (hO.mem_nhds (by simpa [G.lift_base] using hzO a ha)),
      continuous_fst.continuousAt.eventually (G.open_V.mem_nhds G.mem_V)] with p hp hv
    exact ⟨hp, G.lift_mem hv⟩
  have hbase : (a, (0 : E)) ∈ O ∩ tangentBundle M := ⟨hzO a ha, ha, (tangentSpace M a).zero_mem⟩
  filter_upwards [hclose, hparam] with p hp hc
  intro v hv
  exact projector_coordinates (D (a, 0)) (D (tangentLift G.g p))
    ((hdim _ hbase).trans (hdim _ hc).symm) hp hv

lemma native_branch (hk : 2 ≤ k) (hd : d ≤ Module.finrank ℝ E)
    (ha : a ∈ M) (hD : IsRetractor k d M D) :
    ∃ b : S × S → S × D (a, 0), b (0, 0) = (0, 0) ∧
      ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) b (0, 0) ∧
      (∀ᶠ p in 𝓝 ((0, 0) : S × S), retractorEquation G.g (G.correctionMap D) (p, b p) = 0) ∧
      (∀ᶠ v in 𝓝 (((0, 0), (0, 0)) : (S × S) × (S × D (a, 0))),
        retractorEquation G.g (G.correctionMap D) v = 0 ↔ b v.1 = v.2) := by
  have hg := G.smooth_g.contDiffAt (G.open_V.mem_nhds G.mem_V)
  have hQ := G.correction_smooth_base D (by omega) ha hD
  have hdis : D (a, 0) ⊓ (fderiv ℝ G.g 0).toLinearMap.range = ⊥ := by
    rw [← G.tangent 0 G.mem_V, G.g_zero]
    exact hD.choose_spec.2.2.2.2 a ha
  have hdim : Module.finrank ℝ S + Module.finrank ℝ (D (a, 0)) = Module.finrank ℝ E := by
    obtain ⟨O, _, hO, hdim, _, _⟩ := hD
    rw [G.dimension, hdim (a, 0) ⟨hO a ha, ha, (tangentSpace M a).zero_mem⟩]
    omega
  have hinv := transverse_difference_invertible (fderiv ℝ G.g 0) (D (a, 0))
    (G.injective 0 G.mem_V) hdis hdim
  apply retractorEquation_branch hk hg hQ
  simpa only [G.correction_base D] using hinv

end LocalGeometry
end RetractorProof


noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
open ProjLikeRetr.Retractor RandomGradFree.Nonsmooth
variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] {k d : ℕ} {M : Set E} {a : E}

omit [FiniteDimensional ℝ E] in
lemma retractorR_as_correction (D : E × E → Submodule ℝ E) (p : E × E) :
    retractorR M D p = {y | IsMetricProjection (M ∩ {y | y - (p.1 + p.2) ∈ D p}) (p.1 + p.2) y} := by
  have he : {y | ∃ w ∈ D p, y = p.1 + p.2 + w} = {y | y - (p.1 + p.2) ∈ D p} := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hy
      refine ⟨y - (p.1 + p.2), hy, ?_⟩
      abel
  unfold retractorR
  rw [he]

namespace LocalGeometry
variable (G : LocalGeometry (S := S) k d M a) (D : E × E → Submodule ℝ E)

omit [FiniteDimensional ℝ S] in
lemma branch_projection (hk : 2 ≤ k) (ha : a ∈ M) (hD : IsRetractor k d M D)
    (b : S × S → S × D (a, 0)) (hb0 : b (0, 0) = (0, 0))
    (hb : ContinuousAt b (0, 0))
    (heq : ∀ᶠ p in 𝓝 ((0, 0) : S × S), retractorEquation G.g (G.correctionMap D) (p, b p) = 0)
    (hiff : ∀ᶠ v in 𝓝 (((0, 0), (0, 0)) : (S × S) × (S × D (a, 0))),
      retractorEquation G.g (G.correctionMap D) v = 0 ↔ b v.1 = v.2) :
    ∀ᶠ p in 𝓝 ((0, 0) : S × S),
      retractorR M D (tangentLift G.g p) = {G.g (b p).1} := by
  let c : S × S → E := fun p => G.g p.1 + (fderiv ℝ G.g p.1) p.2
  let z : S × S → E := fun p => G.g (b p).1
  obtain ⟨η, hη, hu⟩ := uniform_implicit_uniqueness
    (retractorEquation G.g (G.correctionMap D)) b ((0, 0) : S × S) hiff
  have hg : ContinuousAt G.g 0 := (G.smooth_g.contDiffAt (G.open_V.mem_nhds G.mem_V)).continuousAt
  have hf : ContinuousAt G.f a := (G.smooth_f.contDiffAt (G.open_U.mem_nhds G.mem_U)).continuousAt
  have hcenter : Tendsto c (𝓝 ((0, 0) : S × S)) (𝓝 a) := by
    have hh := (G.lift_smooth (by omega) (p := ((0, 0) : S × S)) G.mem_V).continuousAt
    have hc := hh.fst.add hh.snd
    simpa [c, tangentLift, G.g_zero, Pi.add_def] using hc.tendsto
  have hzt : Tendsto z (𝓝 ((0, 0) : S × S)) (𝓝 a) := by
    have hbt : Tendsto (fun p => (b p).1) (𝓝 ((0, 0) : S × S)) (𝓝 (0 : S)) := by
      simpa [hb0] using hb.fst.tendsto
    simpa [z, G.g_zero, Function.comp_def] using hg.tendsto.comp hbt
  have hbV : ∀ᶠ p in 𝓝 ((0, 0) : S × S), (b p).1 ∈ G.V := by
    have hbt : Tendsto (fun p => (b p).1) (𝓝 ((0, 0) : S × S)) (𝓝 (0 : S)) := by
      simpa [hb0] using hb.fst.tendsto
    exact hbt.eventually (G.open_V.mem_nhds G.mem_V)
  have hfeas : ∀ᶠ p in 𝓝 ((0, 0) : S × S), z p ∈ M ∧ z p - c p ∈ D (tangentLift G.g p) := by
    filter_upwards [heq, hbV] with p hp hv
    refine ⟨(G.g_mem _ hv).1, ?_⟩
    have he : z p - c p = G.correctionMap D p (b p).2 := by
      have h := equation_identity hp
      change z p = c p + G.correctionMap D p (b p).2 at h
      rw [h]; abel
    rw [he]
    exact (D (tangentLift G.g p)).starProjection_apply_mem _
  have hlocal : ∀ᶠ p in 𝓝 ((0, 0) : S × S), ∀ t w, ‖t‖ < η → ‖w‖ < η →
      G.g t = c p + G.correctionMap D p w → G.g t = z p := by
    filter_upwards [hu] with p hp
    intro t w ht hw he
    have hz : retractorEquation G.g (G.correctionMap D) (p, (t, w)) = 0 := by
      change G.g t - G.g p.1 - (fderiv ℝ G.g p.1) p.2 - G.correctionMap D p w = 0
      dsimp [c] at he
      rw [he]; abel
    exact (congrArg (fun v : S × D (a, 0) => G.g v.1) (hp t w ht hw hz)).symm
  have hchart : ∀ᶠ y in 𝓝 a, y ∈ M → G.g (G.f y) = y := by
    filter_upwards [G.open_U.mem_nhds G.mem_U] with y hy
    exact fun hym => G.gf y ⟨hym, hy⟩
  have hresult := eventual_nearest_from_chart M a G.g G.f c z
    (fun p w => G.correctionMap D p w) (fun p => (D (tangentLift G.g p) : Set E))
    η hη hf G.f_base hchart hcenter hzt hfeas (G.correction_representation D (by omega) ha hD) hlocal
  filter_upwards [hresult] with p hp
  rw [retractorR_as_correction]
  exact hp

end LocalGeometry
end RetractorProof


noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
open ProjLikeRetr.Retractor
variable {E S W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem fiber_derivative_rigidity {M : Set E} {g : S → E} {q : S}
    {t : S → S} {w : S → W} {Q : S → W →L[ℝ] E}
    {T : S →L[ℝ] S} {G : S →L[ℝ] E} {W' : S →L[ℝ] W}
    {Q' : S →L[ℝ] (W →L[ℝ] E)} (D : Submodule ℝ E)
    (hg : HasFDerivAt g G q) (ht : HasFDerivAt t T 0)
    (hw : HasFDerivAt w W' 0) (hQ : HasFDerivAt Q Q' 0)
    (ht0 : t 0 = q) (hw0 : w 0 = 0)
    (hT : LinearMap.range G.toLinearMap ≤ tangentSpace M (g q))
    (hQD : ∀ v, Q 0 v ∈ D) (hdis : D ⊓ tangentSpace M (g q) = ⊥)
    (heq : (fun h => g (t h)) =ᶠ[𝓝 0] (fun h => g q + G h + Q h (w h))) :
    HasFDerivAt (fun h => g (t h)) G 0 := by
  have hleft : HasFDerivAt (fun h => g (t h)) (G.comp T) 0 := by
    have hg' : HasFDerivAt g G (t 0) := by simpa [ht0] using hg
    exact hg'.comp 0 ht
  have hright : HasFDerivAt (fun h => g q + G h + Q h (w h))
      (G + (Q 0).comp W') 0 := by
    simpa [hw0, Pi.add_def] using (G.hasFDerivAt.const_add (g q)).add (hQ.clm_apply hw)
  have hid : G.comp T = G + (Q 0).comp W' :=
    hleft.unique (hright.congr_of_eventuallyEq heq)
  have he : G.comp T = G := by
    ext v
    have hv : G (T v) = G v + Q 0 (W' v) := congrArg (fun L : S →L[ℝ] E => L v) hid
    have hm : Q 0 (W' v) ∈ D ⊓ tangentSpace M (g q) := by
      refine ⟨hQD _, ?_⟩
      have hsub := (tangentSpace M (g q)).sub_mem (hT ⟨T v, rfl⟩) (hT ⟨v, rfl⟩)
      change G (T v) - G v ∈ tangentSpace M (g q) at hsub
      have heqv : G (T v) - G v = Q 0 (W' v) := by rw [hv]; abel
      rwa [heqv] at hsub
    rw [hdis] at hm
    have hz : Q 0 (W' v) = 0 := by simpa using hm
    simpa [hz] using hv
  rwa [he] at hleft

end RetractorProof


noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
open ProjLikeRetr.Retractor
variable {E S W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {k d : ℕ} {M : Set E} {a : E}

theorem LocalGeometry.branch_fiber_derivative (G : LocalGeometry (S := S) k d M a)
    (hk : 1 ≤ k) {q : S} (hq : q ∈ G.V) (b : S × S → S × W)
    (Q : S × S → W →L[ℝ] E) (D : Submodule ℝ E)
    (hb : DifferentiableAt ℝ b (q, 0)) (hQ : DifferentiableAt ℝ Q (q, 0))
    (hb0 : b (q, 0) = (q, 0))
    (hQD : ∀ v, Q (q, 0) v ∈ D) (hdis : D ⊓ tangentSpace M (G.g q) = ⊥)
    (heq : ∀ᶠ p in 𝓝 (q, 0),
      G.g (b p).1 = G.g p.1 + fderiv ℝ G.g p.1 p.2 + Q p (b p).2) :
    HasFDerivAt (fun h => G.g (b (q, h)).1) (fderiv ℝ G.g q) 0 := by
  have hpair : HasFDerivAt (fun h : S => (q, h)) (ContinuousLinearMap.inr ℝ S S) 0 :=
    (hasFDerivAt_const q (0 : S)).prodMk (hasFDerivAt_id (0 : S))
  have hb' := hb.hasFDerivAt.comp (0 : S) hpair
  have ht := (ContinuousLinearMap.fst ℝ S W).hasFDerivAt.comp (0 : S) hb'
  have hw := (ContinuousLinearMap.snd ℝ S W).hasFDerivAt.comp (0 : S) hb'
  have hQ' := hQ.hasFDerivAt.comp (0 : S) hpair
  have hg := (G.smooth_g.contDiffAt (G.open_V.mem_nhds hq)).differentiableAt
    (by simpa using (show k ≠ 0 by omega))
  have he : (fun h => G.g (b (q, h)).1) =ᶠ[𝓝 0]
      (fun h => G.g q + fderiv ℝ G.g q h + Q (q, h) (b (q, h)).2) :=
    hpair.continuousAt.tendsto.eventually heq
  apply fiber_derivative_rigidity D hg.hasFDerivAt ht hw hQ'
      (congrArg Prod.fst hb0) (congrArg Prod.snd hb0) ?_ hQD hdis he
  rw [G.tangent q hq]

theorem LocalGeometry.tangent_pullback_derivative (G : LocalGeometry (S := S) k d M a)
    {x : E} (hx : x ∈ M ∩ G.U) {z : S → E}
    (hz : HasFDerivAt z (fderiv ℝ G.g (G.f x)) 0) :
    HasFDerivAt (fun u : tangentSpace M x => z (fderiv ℝ G.f x (u : E)))
      (tangentSpace M x).subtypeL 0 := by
  let L : tangentSpace M x →L[ℝ] S := (fderiv ℝ G.f x).comp (tangentSpace M x).subtypeL
  have he : (fderiv ℝ G.g (G.f x)).comp L = (tangentSpace M x).subtypeL := by
    ext u
    exact G.derivative_gf x hx u u.property
  have hz' : HasFDerivAt z (fderiv ℝ G.g (G.f x)) (L 0) := by simpa using hz
  have hc := hz'.comp (0 : tangentSpace M x) L.hasFDerivAt
  rw [he] at hc
  simpa only [Function.comp_def, L, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using hc

end RetractorProof


set_option maxHeartbeats 800000

noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
open ProjLikeRetr.Retractor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma retraction_of_eventual_data {k : ℕ} {M : Set E} {D : E × E → Submodule ℝ E}
    {a : E} (ha : a ∈ M) (r : E × E → E)
    (hr : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) r (a, 0))
    (hp : ∀ᶠ p in 𝓝 (a, (0 : E)), p ∈ tangentBundle M → retractorR M D p = {r p})
    (hz : ∀ᶠ x in 𝓝 a, x ∈ M → r (x, 0) = x ∧
      HasFDerivAt (fun u : tangentSpace M x => r (x, (u : E))) (tangentSpace M x).subtypeL 0) :
    (∀ᶠ p in 𝓝[tangentBundle M] (a, 0), retractorR M D p = {r p}) ∧
      IsRetractionAt k M r a := by
  refine ⟨eventually_nhdsWithin_iff.mpr hp, ha, ?_⟩
  have hs := hr.eventually (by simp)
  have hz' : ∀ᶠ p in 𝓝 (a, (0 : E)), p.1 ∈ M → r (p.1, 0) = p.1 ∧
      HasFDerivAt (fun u : tangentSpace M p.1 => r (p.1, (u : E))) (tangentSpace M p.1).subtypeL 0 :=
    (continuous_fst.tendsto (a, (0 : E))).eventually hz
  have hall := hp.and (hs.and hz')
  obtain ⟨O, hOsub, hO, haO⟩ := _root_.eventually_nhds_iff.mp hall
  refine ⟨O, hO, haO, ?_, ?_, ?_, ?_⟩
  · intro p hpO
    have he := (hOsub p hpO.1).1 hpO.2
    have hm : r p ∈ retractorR M D p := by rw [he]; exact mem_singleton _
    exact hm.1.1
  · intro p hpO
    exact (hOsub p hpO.1).2.1.contDiffWithinAt
  · intro x hx
    exact ((hOsub (x, 0) hx.1).2.2 hx.2.1).1
  · intro x hx
    exact ((hOsub (x, 0) hx.1).2.2 hx.2.1).2

end RetractorProof


noncomputable section
open Set Filter
open scoped Topology
namespace RetractorProof
open ProjLikeRetr.Retractor
variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] {k d : ℕ} {M : Set E} {a : E}
namespace LocalGeometry
variable (G : LocalGeometry (S := S) k d M a) (D : E × E → Submodule ℝ E)

def branchMap (b : S × S → S × D (a, 0)) (p : E × E) : E :=
  G.g (b (tangentLift G.f p)).1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ S] in
lemma coord_base : tangentLift G.f (a, (0 : E)) = (0, 0) := by
  simp [tangentLift, G.f_base]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ S] in
lemma branchMap_smooth (hk : 1 ≤ k) (b : S × S → S × D (a, 0))
    (hb0 : b (0, 0) = (0, 0))
    (hb : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) b (0, 0)) :
    ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (G.branchMap D b) (a, 0) := by
  have hκ := G.coord_smooth hk (p := (a, (0 : E))) G.mem_U
  have hbκ : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun p => b (tangentLift G.f p)) (a, (0 : E)) := by
    apply ContDiffAt.comp (a, (0 : E)) _ hκ
    simpa only [G.coord_base] using hb
  have hfst : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun p => (b (tangentLift G.f p)).1) (a, (0 : E)) :=
    contDiffAt_fst.comp (a, (0 : E)) hbκ
  have hg := (G.smooth_g.contDiffAt (G.open_V.mem_nhds G.mem_V)).of_le
    (show ((k - 1 : ℕ) : WithTop ℕ∞) ≤ k by exact_mod_cast Nat.sub_le k 1)
  apply ContDiffAt.comp (a, (0 : E)) _ hfst
  simpa only [G.coord_base, hb0] using hg

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ S] in
lemma branchMap_projection (hk : 1 ≤ k) (b : S × S → S × D (a, 0))
    (hp : ∀ᶠ p in 𝓝 ((0, 0) : S × S), retractorR M D (tangentLift G.g p) = {G.g (b p).1}) :
    ∀ᶠ p in 𝓝 (a, (0 : E)), p ∈ tangentBundle M → retractorR M D p = {G.branchMap D b p} := by
  have hκ : Tendsto (tangentLift G.f) (𝓝 (a, (0 : E))) (𝓝 ((0, 0) : S × S)) := by
    simpa only [G.coord_base] using (G.coord_smooth hk (p := (a, (0 : E))) G.mem_U).continuousAt.tendsto
  filter_upwards [hκ.eventually hp,
    continuous_fst.continuousAt.eventually (G.open_U.mem_nhds G.mem_U)] with p hproj hu
  intro hpTM
  rw [G.lift_coord hpTM hu] at hproj
  exact hproj

omit [FiniteDimensional ℝ S] in
lemma branchMap_zero_derivative (hk : 2 ≤ k) (ha : a ∈ M) (hD : IsRetractor k d M D)
    (b : S × S → S × D (a, 0))
    (hb : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) b (0, 0))
    (heq : ∀ᶠ p in 𝓝 ((0, 0) : S × S), retractorEquation G.g (G.correctionMap D) (p, b p) = 0)
    (hiff : ∀ᶠ v in 𝓝 (((0, 0), (0, 0)) : (S × S) × (S × D (a, 0))),
      retractorEquation G.g (G.correctionMap D) v = 0 ↔ b v.1 = v.2) :
    ∀ᶠ x in 𝓝 a, x ∈ M → G.branchMap D b (x, 0) = x ∧
      HasFDerivAt (fun u : tangentSpace M x => G.branchMap D b (x, (u : E)))
        (tangentSpace M x).subtypeL 0 := by
  have hm : ((k - 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show k - 1 ≠ 0 by omega)
  have hpair : Continuous (fun q : S => (q, (0 : S))) := by fun_prop
  have hbe := hpair.continuousAt.tendsto.eventually (hb.eventually (by simp))
  have hQs := G.correction_smooth_base D (by omega) ha hD
  have hQe := hpair.continuousAt.tendsto.eventually (hQs.eventually (by simp))
  have heqe := hpair.continuousAt.tendsto.eventually heq.eventually_nhds
  have hzero := equation_zero_section hiff
  have hall : ∀ᶠ q in 𝓝 (0 : S), q ∈ G.V ∧ b (q, 0) = (q, 0) ∧
      DifferentiableAt ℝ b (q, 0) ∧ DifferentiableAt ℝ (G.correctionMap D) (q, 0) ∧
      (∀ᶠ p in 𝓝 (q, 0), retractorEquation G.g (G.correctionMap D) (p, b p) = 0) := by
    filter_upwards [G.open_V.mem_nhds G.mem_V, hzero, hbe, hQe, heqe] with q hq hz hbs hqs he
    exact ⟨hq, hz, hbs.differentiableAt hm, hqs.differentiableAt hm, he⟩
  have hf : Tendsto G.f (𝓝 a) (𝓝 (0 : S)) := by
    simpa only [G.f_base] using (G.smooth_f.contDiffAt (G.open_U.mem_nhds G.mem_U)).continuousAt.tendsto
  filter_upwards [hf.eventually hall, G.open_U.mem_nhds G.mem_U] with x hx hu
  intro hxM
  have hgfx := G.gf x ⟨hxM, hu⟩
  refine ⟨?_, ?_⟩
  · simpa only [branchMap, tangentLift, map_zero, hx.2.1] using hgfx
  · have hQD : ∀ v, G.correctionMap D (G.f x, 0) v ∈ D (x, 0) := by
      intro v
      have hh : tangentLift G.g (G.f x, 0) = (x, 0) := by simp [tangentLift, hgfx]
      simpa only [correctionMap, hh, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using
        (D (x, 0)).starProjection_apply_mem (v : E)
    have hdis : D (x, 0) ⊓ tangentSpace M (G.g (G.f x)) = ⊥ := by
      rw [hgfx]
      exact hD.choose_spec.2.2.2.2 x hxM
    have hder := G.branch_fiber_derivative (by omega) hx.1 b (G.correctionMap D) (D (x, 0))
      hx.2.2.1 hx.2.2.2.1 hx.2.1 hQD hdis
      (hx.2.2.2.2.mono fun p hp => equation_identity hp)
    have hfinal := G.tangent_pullback_derivative ⟨hxM, hu⟩ hder
    simpa only [branchMap, tangentLift] using hfinal

end LocalGeometry
end RetractorProof


noncomputable section
open Filter
open scoped Topology
namespace RetractorProof
open ProjLikeRetr.Retractor

lemma native_retractor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (D : E × E → Submodule ℝ E)
    (hk : 2 ≤ k) (hM : IsSubmanifold k d M) (hD : IsRetractor k d M D) :
    ∀ a ∈ M, ∃ r : E × E → E,
      (∀ᶠ p in 𝓝[tangentBundle M] (a, 0), retractorR M D p = {r p}) ∧
        IsRetractionAt k M r a := by
  intro a ha
  obtain ⟨G⟩ := localGeometry_exists (show 1 ≤ k by omega) (hM a ha)
  obtain ⟨b, hb0, hb, heq, hiff⟩ := G.native_branch D hk (hM a ha).1 ha hD
  refine ⟨G.branchMap D b, retraction_of_eventual_data ha _ ?_ ?_ ?_⟩
  · exact G.branchMap_smooth D (by omega) b hb0 hb
  · exact G.branchMap_projection D (by omega) b
      (G.branch_projection D hk ha hD b hb0 hb.continuousAt heq hiff)
  · exact G.branchMap_zero_derivative D hk ha hD b hb heq hiff

end RetractorProof


open Filter Topology

namespace ProjLikeRetr.Retractor

/-- Theorem 4.2, pp. 15–16 (retractors give retractions). Let `M` be a `d`-dimensional `C^k`
submanifold (`k ≥ 2`) of the Euclidean space `E` and `D` a retractor on `M`. For every
`x̄ ∈ M`, the set `R(x, u)` of points of `M ∩ (x + u + D(x, u))` nearest to `x + u` is a
singleton `{r(x, u)}` for all `(x, u)` of `TM` near `(x̄, 0)`, and `r` is a retraction on `M`
around `x̄`. Hence `R` is a retraction on `M`. -/
theorem retractor_gives_retraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (D : E × E → Submodule ℝ E)
    (hk : 2 ≤ k) (hM : IsSubmanifold k d M) (hD : IsRetractor k d M D) :
    ∀ xbar ∈ M, ∃ r : E × E → E,
      (∀ᶠ p in 𝓝[tangentBundle M] (xbar, 0), retractorR M D p = {r p}) ∧
      IsRetractionAt k M r xbar := by
  exact RetractorProof.native_retractor k d M D hk hM hD

end ProjLikeRetr.Retractor

open ProjLikeRetr.Retractor

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (D : E × E → Submodule ℝ E)
    (hk : 2 ≤ k) (hM : IsSubmanifold k d M) (hD : IsRetractor k d M D) :
    ∀ xbar ∈ M, ∃ r : E × E → E,
      (∀ᶠ p in 𝓝[tangentBundle M] (xbar, 0), retractorR M D p = {r p}) ∧
      IsRetractionAt k M r xbar := ProjLikeRetr.Retractor.retractor_gives_retraction k d M D hk hM hD
