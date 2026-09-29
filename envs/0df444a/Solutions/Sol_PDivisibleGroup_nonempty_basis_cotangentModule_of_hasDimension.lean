-- Prove2me | solution 1 for PDivisibleGroup.nonempty_basis_cotangentModule_of_hasDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f26beec3-1276-5682-834e-5a68e6fb8838

import Mathlib
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension

set_option autoImplicit false

open Function

namespace PDivDimLim

section Generic

variable {R : Type*} [CommRing R]

theorem ker_eq_ker_of_surjective {P Q F : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module R Q] [AddCommGroup F] [Module R F] [Module.Finite R F]
    (π : P →ₗ[R] F) (hπ : Surjective π) (φ : P →ₗ[R] Q) (hφ : Surjective φ) (e : Q ≃ₗ[R] F)
    (hle : LinearMap.ker π ≤ LinearMap.ker φ) : LinearMap.ker φ = LinearMap.ker π := by
  set ρ : P →ₗ[R] F := e.toLinearMap.comp φ with hρ
  have hkerρ : LinearMap.ker ρ = LinearMap.ker φ := by
    rw [hρ, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
  have hleρ : LinearMap.ker π ≤ LinearMap.ker ρ := hkerρ ▸ hle
  let g : F →ₗ[R] F :=
    ((LinearMap.ker π).liftQ ρ hleρ).comp (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
  have hg : ∀ x, g (π x) = ρ x := by
    intro x
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  have hgsurj : Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := (e.surjective.comp hφ) y
    exact ⟨π x, hg x⟩
  have hginj : Injective g := OrzechProperty.injective_of_surjective_endomorphism g hgsurj
  rw [← hkerρ]
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    have h1 : g (π x) = g 0 := by rw [hg x, hx, map_zero]
    exact hginj h1
  · intro hx
    rw [← hg x, hx, map_zero]

theorem ker_eq_map_ker_comp {P P' Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup P']
    [Module R P'] [AddCommGroup Q] [Module R Q] (s : P' →ₗ[R] P) (hs : Surjective s)
    (t : P →ₗ[R] Q) : LinearMap.ker t = (LinearMap.ker (t.comp s)).map s := by
  rw [LinearMap.ker_comp, Submodule.map_comap_eq_of_surjective hs]

theorem mem_smul_top_pi_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Ideal R) (x : ι → R) :
    x ∈ (J • ⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx i
    have h1 : x i ∈ (J • ⊤ : Submodule R (ι → R)).map (LinearMap.proj i : (ι → R) →ₗ[R] R) :=
      ⟨x, hx, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i),
      Ideal.smul_eq_mul, Ideal.mul_top] at h1
    exact h1
  · intro hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : (Pi.single i (x i) : ι → R) = x i • (Pi.single i 1 : ι → R) := by
      ext j
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij]
    rw [h1]
    exact Submodule.smul_mem_smul (hx i) Submodule.mem_top

def red (ι : Type*) (J : Ideal R) : (ι → R) →ₗ[R] (ι → R ⧸ J) :=
  LinearMap.pi fun i => J.mkQ ∘ₗ LinearMap.proj i

@[scoped simp] theorem red_apply {ι : Type*} (J : Ideal R) (x : ι → R) (i : ι) :
    red ι J x i = Ideal.Quotient.mk J (x i) := rfl

theorem red_surjective (ι : Type*) (J : Ideal R) : Surjective (red ι J) := by
  intro y
  refine ⟨fun i => (Ideal.Quotient.mk_surjective (y i)).choose, funext fun i => ?_⟩
  rw [red_apply]
  exact (Ideal.Quotient.mk_surjective (y i)).choose_spec

theorem ker_red {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Ideal R) :
    LinearMap.ker (red ι J) = J • ⊤ := by
  ext x
  rw [LinearMap.mem_ker, mem_smul_top_pi_iff]
  constructor
  · intro hx i
    have h1 := congr_fun hx i
    rw [red_apply, Pi.zero_apply] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  · intro hx
    funext i
    rw [red_apply, Pi.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hx i)

theorem smul_eq_zero_of_equiv {ι M : Type*} [AddCommGroup M] [Module R M] (J : Ideal R)
    (e : M ≃ₗ[R] (ι → R ⧸ J)) {r : R} (hr : r ∈ J) (m : M) : r • m = 0 := by
  apply e.injective
  rw [map_smul, map_zero]
  funext i
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e m i)
  rw [Pi.smul_apply, Pi.zero_apply, ← ha, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (J.mul_mem_right a hr)

theorem smul_top_le_ker_of_equiv {ι M P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P]
    [Module R P] (J : Ideal R) (e : M ≃ₗ[R] (ι → R ⧸ J)) (φ : P →ₗ[R] M) :
    (J • ⊤ : Submodule R P) ≤ LinearMap.ker φ := by
  refine Submodule.smul_le.mpr fun r hr x _ => ?_
  rw [LinearMap.mem_ker, map_smul]
  exact smul_eq_zero_of_equiv J e hr (φ x)

theorem map_equiv_smul_top {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (e : M ≃ₗ[R] N) :
    (J • ⊤ : Submodule R M).map e.toLinearMap = J • ⊤ := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

end Generic

section Main

variable {R : Type} [CommRing R]

def J (R : Type) [CommRing R] (p v : ℕ) : Ideal R := Ideal.span {(p : R) ^ v}

theorem J_le_J (p : ℕ) {v w : ℕ} (hvw : v ≤ w) : J R p w ≤ J R p v :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hvw)

theorem J_le_pow (p : ℕ) (I : Ideal R) (hp : (p : R) ∈ I) (v : ℕ) : J R p v ≤ I ^ v :=
  (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.pow_mem_pow hp v)

theorem J_le_jacobson (p : ℕ) (I : Ideal R) [IsAdicComplete I R] (hp : (p : R) ∈ I) {v : ℕ}
    (hv : 0 < v) : J R p v ≤ (⊥ : Ideal R).jacobson :=
  (Ideal.span_singleton_le_iff_mem _).mpr
    (Ideal.pow_mem_of_mem _ (IsAdicComplete.le_jacobson_bot I hp) v hv)

def redFac (p n v : ℕ) : (Fin n → R ⧸ J R p (v + 1)) →ₗ[R] (Fin n → R ⧸ J R p v) :=
  LinearMap.pi fun i =>
    (Ideal.Quotient.factorₐ R (J_le_J p (Nat.le_succ v))).toLinearMap ∘ₗ LinearMap.proj i

theorem redFac_comp_red (p n v : ℕ) :
    (redFac (R := R) p n v).comp (red (Fin n) (J R p (v + 1))) = red (Fin n) (J R p v) := by
  ext x i
  rfl

theorem redFac_surjective (p n v : ℕ) : Surjective (redFac (R := R) p n v) := by
  have h1 := red_surjective (R := R) (Fin n) (J R p v)
  rw [← redFac_comp_red p n v, LinearMap.coe_comp] at h1
  exact Surjective.of_comp h1

theorem ker_redFac (p n v : ℕ) : LinearMap.ker (redFac (R := R) p n v) = J R p v • ⊤ := by
  rw [ker_eq_map_ker_comp (red (Fin n) (J R p (v + 1))) (red_surjective _ _) (redFac p n v),
    redFac_comp_red, ker_red, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (red_surjective _ _)]

variable {p h : ℕ} (G : PDivisibleGroup R p h) {n : ℕ} (hn : G.HasDimension n)
include hn

noncomputable def ψ (v : ℕ) : G.Cotangent v ≃ₗ[R] (Fin n → R ⧸ J R p v) := (hn v).some

theorem finite_cotangent (v : ℕ) : Module.Finite R (G.Cotangent v) :=
  Module.Finite.equiv (ψ G hn v).symm

theorem smul_top_le_ker {P : Type*} [AddCommGroup P] [Module R P] (v : ℕ)
    (φ : P →ₗ[R] G.Cotangent v) : (J R p v • ⊤ : Submodule R P) ≤ LinearMap.ker φ :=
  smul_top_le_ker_of_equiv _ (ψ G hn v) φ

theorem subsingleton_cotangent_zero : Subsingleton (G.Cotangent 0) := by
  haveI : Subsingleton (Fin n → R ⧸ J R p 0) := by
    rw [J, pow_zero, Ideal.span_singleton_one]
    infer_instance
  exact (ψ G hn 0).toEquiv.subsingleton

theorem ker_cotangentMap (v : ℕ) :
    LinearMap.ker (G.cotangentMap v) = J R p v • ⊤ := by
  haveI : Module.Finite R (Fin n → R ⧸ J R p v) := inferInstance

  let π : G.Cotangent (v + 1) →ₗ[R] (Fin n → R ⧸ J R p v) :=
    (redFac p n v).comp (ψ G hn (v + 1)).toLinearMap
  have hπ : Surjective π := (redFac_surjective p n v).comp (ψ G hn (v + 1)).surjective
  have hkerπ : LinearMap.ker π = J R p v • ⊤ := by
    change LinearMap.ker ((redFac p n v).comp (ψ G hn (v + 1)).toLinearMap) = _
    rw [LinearMap.ker_comp, ker_redFac]
    rw [show (ψ G hn (v + 1)).toLinearMap = ((ψ G hn (v + 1) : G.Cotangent (v + 1) →ₗ[R] _)) from rfl,
      Submodule.comap_equiv_eq_map_symm]
    exact map_equiv_smul_top (J R p v) (ψ G hn (v + 1)).symm
  rw [← hkerπ]
  refine ker_eq_ker_of_surjective π hπ (G.cotangentMap v) (G.cotangentMap_surjective v) (ψ G hn v) ?_
  rw [hkerπ]
  exact smul_top_le_ker G hn v _

noncomputable def phiOne : (Fin n → R) →ₗ[R] G.Cotangent 1 :=
  (ψ G hn 1).symm.toLinearMap ∘ₗ red (Fin n) (J R p 1)

theorem phiOne_surjective : Surjective (phiOne G hn) :=
  (ψ G hn 1).symm.surjective.comp (red_surjective _ _)

omit hn in

noncomputable def lift (v : ℕ) (φ : (Fin n → R) →ₗ[R] G.Cotangent v) :
    (Fin n → R) →ₗ[R] G.Cotangent (v + 1) :=
  (Pi.basisFun R (Fin n)).constr R fun i =>
    (G.cotangentMap_surjective v (φ (Pi.basisFun R (Fin n) i))).choose

omit hn in
theorem cotangentMap_comp_lift (v : ℕ) (φ : (Fin n → R) →ₗ[R] G.Cotangent v) :
    (G.cotangentMap v).comp (lift G v φ) = φ := by
  refine (Pi.basisFun R (Fin n)).ext fun i => ?_
  rw [LinearMap.comp_apply, lift, Module.Basis.constr_basis]
  exact (G.cotangentMap_surjective v (φ (Pi.basisFun R (Fin n) i))).choose_spec

noncomputable def phi : (v : ℕ) → ((Fin n → R) →ₗ[R] G.Cotangent v)
  | 0 => 0
  | 1 => phiOne G hn
  | v + 2 => lift G (v + 1) (phi (v + 1))

theorem phi_zero : phi G hn 0 = 0 := rfl
theorem phi_one : phi G hn 1 = phiOne G hn := rfl
theorem phi_succ_succ (v : ℕ) : phi G hn (v + 2) = lift G (v + 1) (phi G hn (v + 1)) := rfl

theorem cotangentMap_comp_phi (v : ℕ) : (G.cotangentMap v).comp (phi G hn (v + 1)) = phi G hn v := by
  cases v with
  | zero =>
    haveI := subsingleton_cotangent_zero G hn
    ext x
    exact Subsingleton.elim _ _
  | succ v =>
    rw [phi_succ_succ, cotangentMap_comp_lift]

theorem cotangentMap_phi (v : ℕ) (x : Fin n → R) :
    G.cotangentMap v (phi G hn (v + 1) x) = phi G hn v x :=
  LinearMap.congr_fun (cotangentMap_comp_phi G hn v) x

omit hn in

theorem smul_top_mono {P : Type*} [AddCommGroup P] [Module R P] {v w : ℕ} (hvw : v ≤ w) :
    (J R p w • ⊤ : Submodule R P) ≤ J R p v • ⊤ :=
  Submodule.smul_mono_left (J_le_J p hvw)

variable (I : Ideal R) [IsAdicComplete I R] (hp : (p : R) ∈ I)
include I hp

theorem lift_surjective (v : ℕ) (φ : (Fin n → R) →ₗ[R] G.Cotangent (v + 1)) (hφ : Surjective φ) :
    Surjective (lift G (v + 1) φ) := by
  haveI := finite_cotangent G hn (v + 2)
  set φ' := lift G (v + 1) φ with hφ'
  have hcomp : (G.cotangentMap (v + 1)).comp φ' = φ := cotangentMap_comp_lift G (v + 1) φ
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := J R p (v + 1)) Module.Finite.fg_top
    (J_le_jacobson p I hp (Nat.succ_pos v)) ?_
  intro y _
  obtain ⟨x, hx⟩ := hφ (G.cotangentMap (v + 1) y)
  have hker : y - φ' x ∈ LinearMap.ker (G.cotangentMap (v + 1)) := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero, ← hx, ← hcomp, LinearMap.comp_apply]
  rw [ker_cotangentMap G hn (v + 1)] at hker
  rw [show y = φ' x + (y - φ' x) by abel]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) hker

theorem phi_succ_surjective (v : ℕ) : Surjective (phi G hn (v + 1)) := by
  induction v with
  | zero => exact phiOne_surjective G hn
  | succ v ih =>
    rw [phi_succ_succ]
    exact lift_surjective G hn I hp v _ ih

theorem phi_surjective (v : ℕ) : Surjective (phi G hn v) := by
  cases v with
  | zero =>
    haveI := subsingleton_cotangent_zero G hn
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  | succ v => exact phi_succ_surjective G hn I hp v

theorem ker_phi (v : ℕ) : LinearMap.ker (phi G hn v) = J R p v • ⊤ := by
  haveI : Module.Finite R (Fin n → R ⧸ J R p v) := inferInstance
  rw [← ker_red (J R p v)]
  refine ker_eq_ker_of_surjective (red (Fin n) (J R p v)) (red_surjective _ _) (phi G hn v)
    (phi_surjective G hn I hp v) (ψ G hn v) ?_
  rw [ker_red]
  exact smul_top_le_ker G hn v _

theorem ker_phi_antitone {v w : ℕ} (hvw : v ≤ w) :
    LinearMap.ker (phi G hn w) ≤ LinearMap.ker (phi G hn v) := by
  rw [ker_phi G hn I hp, ker_phi G hn I hp]
  exact smul_top_mono hvw

omit I hp in
theorem phi_mem_cotangentModule (x : Fin n → R) :
    (fun v => phi G hn v x) ∈ G.cotangentModule := fun v => cotangentMap_phi G hn v x

noncomputable def Phi : (Fin n → R) →ₗ[R] G.cotangentModule where
  toFun x := ⟨fun v => phi G hn v x, phi_mem_cotangentModule G hn x⟩
  map_add' x y := by
    ext v
    change phi G hn v (x + y) = phi G hn v x + phi G hn v y
    rw [map_add]
  map_smul' r x := by
    ext v
    change phi G hn v (r • x) = r • phi G hn v x
    rw [map_smul]

omit I hp in
@[scoped simp] theorem proj_Phi (v : ℕ) (x : Fin n → R) :
    G.cotangentModuleProj v (Phi G hn x) = phi G hn v x := rfl

omit I hp in
theorem proj_comp_Phi (v : ℕ) : (G.cotangentModuleProj v).comp (Phi G hn) = phi G hn v := rfl

theorem Phi_injective : Injective (Phi G hn) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  funext i
  refine IsHausdorff.haus (inferInstance : IsHausdorff I R) (x i) fun v => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  have hv : x ∈ LinearMap.ker (phi G hn v) := by
    rw [LinearMap.mem_ker, ← proj_Phi, hx, map_zero]
  rw [ker_phi G hn I hp v, mem_smul_top_pi_iff] at hv
  exact J_le_pow p I hp v (hv i)

theorem phi_lift_eq (y : G.cotangentModule) (x : ℕ → (Fin n → R))
    (hx : ∀ v, phi G hn v (x v) = (y : ∀ v, G.Cotangent v) v) {w N : ℕ} (hwN : w ≤ N) :
    phi G hn w (x N) = (y : ∀ v, G.Cotangent v) w := by
  induction N, hwN using Nat.le_induction with
  | base => exact hx w
  | succ N hwN ih =>
    rw [← ih, ← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker]
    refine ker_phi_antitone G hn I hp hwN ?_
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero, hx N, ← cotangentMap_phi G hn N, hx (N + 1)]
    exact y.2 N

theorem Phi_surjective [IsNoetherianRing R] : Surjective (Phi G hn) := by
  intro y

  choose x hx using fun v => phi_surjective G hn I hp v ((y : ∀ v, G.Cotangent v) v)

  have hstep : ∀ v i, x (v + 1) i - x v i ∈ I ^ v := by
    intro v i
    have h1 : x (v + 1) - x v ∈ LinearMap.ker (phi G hn v) := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero, hx v]
      exact phi_lift_eq G hn I hp y x hx (Nat.le_succ v)
    rw [ker_phi G hn I hp v, mem_smul_top_pi_iff] at h1
    exact J_le_pow p I hp v (h1 i)

  have hcauchy : ∀ i {m N : ℕ}, m ≤ N → x m i ≡ x N i [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro i m N hmN
    induction N, hmN using Nat.le_induction with
    | base => exact SModEq.rfl
    | succ N hmN ih =>
      refine ih.trans ?_
      rw [SModEq.comm, SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
      exact Ideal.pow_le_pow_right hmN (hstep N i)

  choose L hL using fun i =>
    IsPrecomplete.prec (inferInstance : IsPrecomplete I R) (f := fun v => x v i) (hcauchy i)
  refine ⟨L, Subtype.ext (funext fun w => ?_)⟩
  change phi G hn w L = (y : ∀ v, G.Cotangent v) w

  haveI := finite_cotangent G hn w
  haveI : IsHausdorff I (G.Cotangent w) :=
    IsHausdorff.of_le_jacobson I _ (IsAdicComplete.le_jacobson_bot I)
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff I (G.Cotangent w)) _ fun N => ?_
  rw [SModEq.zero]

  set N' := max N w with hN'
  have h1 : phi G hn w L - (y : ∀ v, G.Cotangent v) w = phi G hn w (L - x N') := by
    rw [map_sub, phi_lift_eq G hn I hp y x hx (le_max_right N w)]
  have h2 : L - x N' ∈ (I ^ N' • ⊤ : Submodule R (Fin n → R)) := by
    rw [mem_smul_top_pi_iff]
    intro i
    have h3 := (hL i N').symm
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h3
    exact h3
  rw [h1]
  have h4 : phi G hn w (L - x N') ∈ (I ^ N' • ⊤ : Submodule R (Fin n → R)).map (phi G hn w) :=
    Submodule.mem_map_of_mem h2
  rw [Submodule.map_smul''] at h4
  exact Submodule.smul_mono (Ideal.pow_le_pow_right (le_max_left N w)) le_top h4

noncomputable def PhiEquiv [IsNoetherianRing R] : (Fin n → R) ≃ₗ[R] G.cotangentModule :=
  LinearEquiv.ofBijective (Phi G hn) ⟨Phi_injective G hn I hp, Phi_surjective G hn I hp⟩

@[scoped simp] theorem PhiEquiv_apply [IsNoetherianRing R] (x : Fin n → R) :
    PhiEquiv G hn I hp x = Phi G hn x := rfl

theorem cotangentModuleProj_surjective (v : ℕ) : Surjective (G.cotangentModuleProj v) := by
  intro m
  obtain ⟨x, hx⟩ := phi_surjective G hn I hp v m
  exact ⟨Phi G hn x, hx⟩

theorem ker_cotangentModuleProj [IsNoetherianRing R] (v : ℕ) :
    LinearMap.ker (G.cotangentModuleProj v) = J R p v • ⊤ := by
  rw [ker_eq_map_ker_comp (PhiEquiv G hn I hp).toLinearMap (PhiEquiv G hn I hp).surjective]
  change ((LinearMap.ker ((G.cotangentModuleProj v).comp (Phi G hn))).map
    (PhiEquiv G hn I hp).toLinearMap) = _
  rw [proj_comp_Phi, ker_phi G hn I hp v]
  exact map_equiv_smul_top (J R p v) (PhiEquiv G hn I hp)

end Main

end PDivDimLim
p2m_reactivate "P2MW.S_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension.PDivDimLim"

theorem solution
    {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {p h : ℕ} (hp : (p : R) ∈ I) (G : PDivisibleGroup R p h) {n : ℕ} (hn : G.HasDimension n) :
    Nonempty (Module.Basis (Fin n) R G.cotangentModule) ∧
      (∀ v, Function.Surjective (G.cotangentModuleProj v)) ∧
      ∀ v, LinearMap.ker (G.cotangentModuleProj v) =
        Ideal.span {(p : R) ^ v} • (⊤ : Submodule R G.cotangentModule) :=
  ⟨⟨(Pi.basisFun R (Fin n)).map (PDivDimLim.PhiEquiv G hn I hp)⟩,
    PDivDimLim.cotangentModuleProj_surjective G hn I hp,
    PDivDimLim.ker_cotangentModuleProj G hn I hp⟩

end S_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension
end P2MW
export P2MW.S_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension (solution)
