-- Prove2me | solution 1 for ProxGapTight.lemma_3_2_base_code
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:49:41.001779+00:00
-- url     : https://prove2.me/submissions/79c6efcd-61cb-4f3e-be3a-37d8908d6aa7

import Mathlib
import Definitions.Def_ProxGapTight_Lines
import Definitions.Def_ProxGapTight_Codim2
import Definitions.Def_ProxGapTight_em
import Definitions.Def_ProxGapTight_nm
import Definitions.Def_ProxGapTight_Um
import Definitions.Def_ProxGapTight_shorten
import Definitions.Def_ProxGapTight_minDist
import Definitions.Def_ProxGapTight_relDist
import Definitions.Def_ProxGapTight_distToCode
import Definitions.Def_ProxGapTight_exceptionalSet
import Definitions.Def_ProxGapTight_Lm
import Definitions.Def_ProxGapTight_incVec
import Theorems.Thm_ProxGapTight_lemma_3_4_shortenings
import Theorems.Thm_ProxGapTight_lemma_3_5_syndromes

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ProxGapTight.Dev.BaseCode1
open ProxGapTight

variable {K : Type} [Field K] [Fintype K] {m : ℕ}

noncomputable def linesIn (U : Submodule K (Fin m → K)) : Finset (Lines K m) := by
  classical
  exact Finset.univ.filter (fun ℓ => ℓ.1 ≤ U)

theorem mem_linesIn (U : Submodule K (Fin m → K)) (ℓ : Lines K m) :
    ℓ ∈ linesIn U ↔ ℓ.1 ≤ U := by
  classical
  simp [linesIn]

theorem card_linesIn (U : Submodule K (Fin m → K)) (d : ℕ) (hd : Module.finrank K U = d) :
    (linesIn U).card = (Fintype.card K ^ d - 1) / (Fintype.card K - 1) := by
  classical
  let f : Projectivization K U → Lines K m := fun v =>
    ⟨v.submodule.map U.subtype, by
      rw [← v.finrank_submodule]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective U.subtype U.injective_subtype _).symm)⟩
  have hinj : Function.Injective f := by
    intro v w h
    apply Projectivization.submodule_injective
    have := congrArg Subtype.val h
    simp only [f] at this
    exact Submodule.map_injective_of_injective U.injective_subtype this
  haveI : Finite (Projectivization K U) := Finite.of_injective f hinj
  haveI : Fintype (Projectivization K U) := Fintype.ofFinite _
  have himg : (linesIn U) = Finset.univ.image f := by
    ext ℓ
    rw [mem_linesIn]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hle
      let H : Submodule K U := ℓ.1.comap U.subtype
      have hH : H.map U.subtype = ℓ.1 := by
        rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hle
      have hf1 : Module.finrank K H = 1 := by
        rw [← ℓ.2, ← hH]
        exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective U.subtype U.injective_subtype H))
      refine ⟨Projectivization.mk'' H hf1, ?_⟩
      apply Subtype.ext
      simp only [f, Projectivization.submodule_mk'', hH]
    · rintro ⟨v, rfl⟩
      simp only [f]
      exact Submodule.map_subtype_le U _
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have := Projectivization.card'' K U
  rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card (α := K)]
  have hc : Nat.card U = Fintype.card K ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := U), hd, Nat.card_eq_fintype_card]
  rw [hc]

theorem card_lines (m : ℕ) : Fintype.card (Lines K m) = nm (Fintype.card K) m := by
  classical
  have h : (linesIn (⊤ : Submodule K (Fin m → K))) = Finset.univ := by
    ext ℓ; simp [mem_linesIn]
  have := card_linesIn (⊤ : Submodule K (Fin m → K)) m (by simp)
  rw [h, Finset.card_univ] at this
  simpa [nm] using this

theorem card_linesIn_codim2 (W : Codim2 K m) :
    (linesIn W.1).card = em (Fintype.card K) m := by
  unfold em
  apply card_linesIn
  have := W.2
  omega

theorem single_eq {ι : Type} [DecidableEq ι] (i : ι) (x : K) :
    (Pi.single i x : ι → K) = x • (Pi.single i (1 : K) : ι → K) := by
  ext j
  by_cases h : j = i <;> simp [Pi.single_apply, h]

theorem exists_ker (W : Codim2 K m) :
    ∃ T : (Fin m → K) →ₗ[K] (Fin 2 → K), LinearMap.ker T = W.1 := by
  have h1 := Submodule.finrank_quotient_add_finrank W.1
  have hq : Module.finrank K ((Fin m → K) ⧸ W.1) = Module.finrank K (Fin 2 → K) := by
    simp only [Module.finrank_fin_fun] at h1 ⊢
    have := W.2
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hq
  refine ⟨e.toLinearMap ∘ₗ W.1.mkQ, ?_⟩
  rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

theorem card_codim2_add_one_le :
    Fintype.card (Codim2 K m) + 1 ≤ Fintype.card K ^ (2 * m) := by
  classical
  choose T hT using (exists_ker (K := K) (m := m))
  let Φ : Codim2 K m → (Fin m → Fin 2 → K) := fun W i => T W (Pi.single i 1)
  have hext : ∀ W W' : Codim2 K m, Φ W = Φ W' → T W = T W' := by
    intro W W' h
    apply LinearMap.pi_ext
    intro i x
    rw [single_eq, map_smul, map_smul]
    exact congrArg (x • ·) (congrFun h i)
  have hinj : Function.Injective Φ := by
    intro W W' h
    apply Subtype.ext
    rw [← hT W, ← hT W', hext W W' h]
  have hnz : ∀ W, Φ W ≠ 0 := by
    intro W h0
    have hT0 : T W = 0 := by
      apply LinearMap.pi_ext
      intro i x
      rw [single_eq, map_smul]
      have h2 : T W (Pi.single i 1) = 0 := congrFun h0 i
      rw [h2]
      simp
    have htop : W.1 = ⊤ := by rw [← hT W, hT0]; simp
    have := W.2
    rw [htop] at this
    simp at this
  have hsub : Finset.univ.image Φ ⊆ Finset.univ.erase 0 := by
    intro f hf
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hf
    obtain ⟨W, rfl⟩ := hf
    simp [hnz W]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (Finset.mem_univ _)] at h1
  simp only [Finset.card_univ] at h1
  have hc : Fintype.card (Fin m → Fin 2 → K) = Fintype.card K ^ (2 * m) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]
  have hpos : 0 < Fintype.card (Fin m → Fin 2 → K) := Fintype.card_pos
  rw [← hc]
  omega

section lower
variable {k : ℕ}

noncomputable def phi (c : Fin k → K) : (Fin (k+2) → K) →ₗ[K] K :=
  ∑ j, c j • (LinearMap.proj (j.succ.succ) : (Fin (k+2) → K) →ₗ[K] K)

theorem phi_apply (c : Fin k → K) (x : Fin (k+2) → K) :
    phi c x = ∑ j, c j * x j.succ.succ := by
  simp [phi, LinearMap.sum_apply]

noncomputable def Tab (a b : Fin k → K) : (Fin (k+2) → K) →ₗ[K] (Fin 2 → K) :=
  LinearMap.pi ![(LinearMap.proj (0 : Fin (k+2)) : (Fin (k+2) → K) →ₗ[K] K) - phi a,
    (LinearMap.proj (1 : Fin (k+2)) : (Fin (k+2) → K) →ₗ[K] K) - phi b]

theorem Tab_apply (a b : Fin k → K) (x : Fin (k+2) → K) :
    Tab a b x = ![x 0 - ∑ j, a j * x j.succ.succ, x 1 - ∑ j, b j * x j.succ.succ] := by
  ext i
  fin_cases i <;> simp [Tab, phi_apply]

theorem Tab_surj (a b : Fin k → K) : Function.Surjective (Tab a b) := by
  intro u
  refine ⟨Fin.cons (u 0) (Fin.cons (u 1) 0), ?_⟩
  rw [Tab_apply]
  ext i
  fin_cases i <;> simp

noncomputable def Wab (a b : Fin k → K) : Codim2 K (k+2) :=
  ⟨LinearMap.ker (Tab a b), by
    have h := LinearMap.finrank_range_add_finrank_ker (Tab a b)
    rw [LinearMap.range_eq_top.mpr (Tab_surj a b)] at h
    simp at h
    omega⟩

theorem mem_Wab (a b : Fin k → K) (x : Fin (k+2) → K) :
    x ∈ (Wab a b).1 ↔ x 0 = ∑ j, a j * x j.succ.succ ∧ x 1 = ∑ j, b j * x j.succ.succ := by
  show x ∈ LinearMap.ker (Tab a b) ↔ _
  rw [LinearMap.mem_ker, Tab_apply]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    exact ⟨by linear_combination h0, by linear_combination h1⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · simp [h0]
    · simp [h1]

theorem Wab_inj (a b a' b' : Fin k → K) (h : Wab a b = Wab a' b') : a = a' ∧ b = b' := by
  have key : ∀ j : Fin k, (Fin.cons (a j) (Fin.cons (b j) (Pi.single j 1)) : Fin (k+2) → K)
      ∈ (Wab a b).1 := by
    intro j
    rw [mem_Wab]
    simp [Pi.single_apply, mul_ite]
  constructor
  · funext j
    have := key j
    rw [h, mem_Wab] at this
    simp [Pi.single_apply, mul_ite] at this
    exact this.1
  · funext j
    have := key j
    rw [h, mem_Wab] at this
    simp [Pi.single_apply, mul_ite] at this
    exact this.2

end lower

theorem card_codim2_ge (hm : 2 ≤ m) :
    Fintype.card K ^ (2 * (m - 2)) ≤ Fintype.card (Codim2 K m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hinj : Function.Injective
      (fun p : (Fin k → K) × (Fin k → K) => Wab p.1 p.2) := by
    intro p q h
    have := Wab_inj _ _ _ _ h
    exact Prod.ext this.1 this.2
  have := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at this
  simpa [two_mul, pow_add] using this

theorem exists_three (hm : 4 ≤ m) (hK : 2 < Fintype.card K) :
    ∃ W1 W2 W3 : Codim2 K m, W1 ≠ W2 ∧ W1 ≠ W3 ∧ W2 ≠ W3 ∧
      ∃ ℓ : Lines K m, ℓ.1 ≤ W1.1 ∧ ℓ.1 ≤ W2.1 ∧ ℓ.1 ≤ W3.1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : 2 ≤ k := by omega
  classical
  obtain ⟨s1, s2, s3, -, -, -, h12, h13, h23⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < (Finset.univ : Finset K).card by simpa using hK)
  let j0 : Fin k := ⟨0, by omega⟩
  let j1 : Fin k := ⟨1, by omega⟩
  have hj : j0 ≠ j1 := by simp [j0, j1, Fin.ext_iff]
  let b : K → Fin k → K := fun s j => if j = j0 then s else 0
  have hb : ∀ s s', Wab (0 : Fin k → K) (b s) = Wab 0 (b s') → s = s' := by
    intro s s' h
    have := (Wab_inj _ _ _ _ h).2
    have := congrFun this j0
    simpa [b] using this
  let e : Fin (k+2) → K := Fin.cons 0 (Fin.cons 0 (Pi.single j1 1))
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h j1.succ.succ
    simp [e] at this
  have hmem : ∀ s, e ∈ (Wab (0 : Fin k → K) (b s)).1 := by
    intro s
    rw [mem_Wab]
    simp [e, b, Pi.single_apply, Ne.symm hj, mul_ite]
  let ℓ : Lines K (k+2) := ⟨Submodule.span K {e}, finrank_span_singleton he0⟩
  have hℓ : ∀ s, ℓ.1 ≤ (Wab (0 : Fin k → K) (b s)).1 := by
    intro s
    simpa [ℓ, Submodule.span_singleton_le_iff_mem] using hmem s
  refine ⟨Wab 0 (b s1), Wab 0 (b s2), Wab 0 (b s3), ?_, ?_, ?_, ℓ, hℓ _, hℓ _, hℓ _⟩
  · exact fun h => h12 (hb _ _ h)
  · exact fun h => h13 (hb _ _ h)
  · exact fun h => h23 (hb _ _ h)

end ProxGapTight.Dev.BaseCode1
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ProxGapTight.Dev.BaseCode2
open ProxGapTight

section basechange
variable (p : ℕ) [Fact p.Prime] {K : Type} [Field K] {m : ℕ}
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod p) F]

/-- `F`-span of the incidence vectors (inside `F^X`). -/
noncomputable def Dm (K : Type) [Field K] (m : ℕ) (F : Type) [Field F] :
    Submodule F (Lines K m → F) :=
  Submodule.span F (Set.range (fun W : Codim2 K m => incVec F W))

theorem incVec_mem_Dm [Fintype K] (W : Codim2 K m) : incVec F W ∈ Dm K m F :=
  Submodule.subset_span ⟨W, rfl⟩

theorem incVec_apply_alg (W : Codim2 K m) (ℓ : Lines K m) :
    incVec F W ℓ = algebraMap (ZMod p) F (incVec (ZMod p) W ℓ) := by
  unfold incVec
  split_ifs <;> simp

/-- coordinatewise embedding `F_p^X → F^X` -/
def iota (K : Type) [Field K] (m : ℕ) (F : Type) [Field F] [Algebra (ZMod p) F]
    (w : Lines K m → ZMod p) : Lines K m → F :=
  fun x => algebraMap (ZMod p) F (w x)

theorem iota_incVec (W : Codim2 K m) : iota p K m F (incVec (ZMod p) W) = incVec F W := by
  ext x
  exact (incVec_apply_alg p (F := F) W x).symm

theorem iota_mem_span [Fintype K] (G : Set (Lines K m → ZMod p)) (w : Lines K m → ZMod p)
    (hw : w ∈ Submodule.span (ZMod p) G) :
    iota p K m F w ∈ Submodule.span F (iota p K m F '' G) := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : iota p K m F 0 = 0 := by ext z; simp [iota]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : iota p K m F (x + y) = iota p K m F x + iota p K m F y := by
      ext z; simp [iota]
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have : iota p K m F (c • x) = algebraMap (ZMod p) F c • iota p K m F x := by
      ext z; simp [iota]
    rw [this]; exact Submodule.smul_mem _ _ hx

theorem base_change [Fintype K] (S : Finset (Lines K m)) (G : Set (Lines K m → ZMod p))
    (hG : shorten (Um K m p) S ≤ Submodule.span (ZMod p) G)
    (v : Lines K m → F) (hv : v ∈ Dm K m F) (hS : ∀ x, x ∉ S → v x = 0) :
    v ∈ Submodule.span F (iota p K m F '' G) := by
  classical
  haveI : Finite F := inferInstance
  haveI : FiniteDimensional (ZMod p) F := Module.Finite.of_finite
  let b := Module.finBasis (ZMod p) F
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hv
  let w : Fin (Module.finrank (ZMod p) F) → Lines K m → ZMod p :=
    fun j x => b.repr (v x) j
  have hwUm : ∀ j, w j ∈ Um K m p := by
    intro j
    have : w j = ∑ W : Codim2 K m, (b.repr (c W) j) • incVec (ZMod p) W := by
      ext x
      simp only [w, ← hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum,
        Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply]
      refine Finset.sum_congr rfl fun W _ => ?_
      rw [incVec_apply_alg p, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
        smul_eq_mul, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun W _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨W, rfl⟩)
  have hwS : ∀ j, w j ∈ supportedOn (ZMod p) S := by
    intro j x hx
    simp [w, hS x hx]
  have hwG : ∀ j, w j ∈ Submodule.span (ZMod p) G := fun j =>
    hG (Submodule.mem_inf.mpr ⟨hwUm j, hwS j⟩)
  have hv' : v = ∑ j, b j • iota p K m F (w j) := by
    ext x
    simp only [Finset.sum_apply, Pi.smul_apply, iota, smul_eq_mul, w]
    conv_lhs => rw [← b.sum_repr (v x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [hv']
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (iota_mem_span p G _ (hwG j))

end basechange

section transfer
variable {R : Type} [Semiring R] [DecidableEq R] {ι ι' : Type} [Fintype ι] [Fintype ι']

theorem hammingDist_comp_equiv (σ : ι' ≃ ι) (x y : ι → R) :
    hammingDist (x ∘ σ) (y ∘ σ) = hammingDist x y := by
  unfold hammingDist
  exact Finset.card_equiv σ (by intro i; simp)

theorem hammingNorm_comp_equiv (σ : ι' ≃ ι) (x : ι → R) :
    hammingNorm (x ∘ σ) = hammingNorm x := by
  have := hammingDist_comp_equiv σ x 0
  simpa [hammingDist_zero_right] using this

variable (σ : ι' ≃ ι)

/-- reindexing of words -/
def reidx (R : Type) [Semiring R] (σ : ι' ≃ ι) : (ι → R) ≃ₗ[R] (ι' → R) :=
  LinearEquiv.funCongrLeft R R σ

theorem minDist_map (C : Submodule R (ι → R)) :
    minDist (C.map (reidx R σ).toLinearMap) = minDist C := by
  unfold minDist
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Submodule.mem_map]
  constructor
  · rintro ⟨c', ⟨c, hc, rfl⟩, h0, hw⟩
    refine ⟨c, hc, ?_, ?_⟩
    · rintro rfl; exact h0 (by simp)
    · rw [← hw]; exact (hammingNorm_comp_equiv σ c).symm
  · rintro ⟨c, hc, h0, hw⟩
    refine ⟨reidx R σ c, ⟨c, hc, rfl⟩, ?_, ?_⟩
    · intro h
      apply h0
      exact (reidx R σ).injective (by simpa using h)
    · rw [← hw]; exact hammingNorm_comp_equiv σ c

theorem distToCode_map (C : Submodule R (ι → R)) (x : ι → R) :
    distToCode (reidx R σ x) (C.map (reidx R σ).toLinearMap) = distToCode x C := by
  unfold distToCode
  have hset : {w : ℕ | ∃ c ∈ C.map (reidx R σ).toLinearMap, hammingDist (reidx R σ x) c = w}
      = {w : ℕ | ∃ c ∈ C, hammingDist x c = w} := by
    ext w
    simp only [Set.mem_setOf_eq, Submodule.mem_map]
    constructor
    · rintro ⟨c', ⟨c, hc, rfl⟩, hw⟩
      exact ⟨c, hc, by rw [← hw]; exact (hammingDist_comp_equiv σ x c).symm⟩
    · rintro ⟨c, hc, hw⟩
      exact ⟨reidx R σ c, ⟨c, hc, rfl⟩, by rw [← hw]; exact hammingDist_comp_equiv σ x c⟩
  rw [hset, Fintype.card_congr σ]

end transfer

end ProxGapTight.Dev.BaseCode2
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ProxGapTight.Dev.BaseCode3
open ProxGapTight ProxGapTight.Dev.BaseCode1 ProxGapTight.Dev.BaseCode2

section aux
variable {K : Type} [Field K] [Fintype K] {m : ℕ} {F : Type} [Field F]

theorem hammingNorm_le_of_subset [DecidableEq F] (x : Lines K m → F) (A : Finset (Lines K m))
    (h : ∀ ℓ, x ℓ ≠ 0 → ℓ ∈ A) : hammingNorm x ≤ A.card := by
  unfold hammingNorm
  apply Finset.card_le_card
  intro ℓ hℓ
  exact h ℓ (by simpa using hℓ)

theorem exists_vec_sep (W W' W'' : Codim2 K m) (h : W ≠ W') (h' : W ≠ W'') :
    ∃ x ∈ W.1, x ∉ W'.1 ∧ x ∉ W''.1 := by
  have hn : ∀ V : Codim2 K m, W ≠ V → ∃ x ∈ W.1, x ∉ V.1 := by
    intro V hV
    by_contra hc
    push Not at hc
    have hle : W.1 ≤ V.1 := hc
    exact hV (Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle
      (by have := W.2; have := V.2; omega)))
  obtain ⟨x, hx, hx'⟩ := hn W' h
  obtain ⟨y, hy, hy'⟩ := hn W'' h'
  by_cases hx2 : x ∈ W''.1
  · by_cases hy2 : y ∈ W'.1
    · refine ⟨x + y, add_mem hx hy, ?_, ?_⟩
      · intro hxy; exact hx' (by simpa using sub_mem hxy hy2)
      · intro hxy; exact hy' (by simpa using sub_mem hxy hx2)
    · exact ⟨y, hy, hy2, hy'⟩
  · exact ⟨x, hx, hx', hx2⟩

theorem line_of_vec (x : Fin m → K) (hx : x ≠ 0) :
    ∃ ℓ : Lines K m, ∀ V : Submodule K (Fin m → K), ℓ.1 ≤ V ↔ x ∈ V := by
  refine ⟨⟨Submodule.span K {x}, finrank_span_singleton hx⟩, fun V => ?_⟩
  simp [Submodule.span_singleton_le_iff_mem]

theorem pair_span (v w : Fin 2 → F) (h : LinearIndependent F ![v, w]) (z : Fin 2 → F) :
    ∃ a b : F, z = a • v + b • w := by
  have hc : Fintype.card (Fin 2) = Module.finrank F (Fin 2 → F) := by simp
  let B := basisOfLinearIndependentOfCardEqFinrank h hc
  refine ⟨B.repr z 0, B.repr z 1, ?_⟩
  have := B.sum_repr z
  rw [Fin.sum_univ_two] at this
  simpa [B, coe_basisOfLinearIndependentOfCardEqFinrank] using this.symm

end aux

section main
variable (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [Fintype K] {m : ℕ} (Q : ℕ)
  {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

theorem low_two
    (h1 : ∀ S : Finset (Lines K m), S.card ≤ Lm Q m →
      ∃ W W' : Codim2 K m, shorten (Um K m p) S ≤
        Submodule.span (ZMod p) {incVec (ZMod p) W, incVec (ZMod p) W'})
    (v : Lines K m → F) (hv : v ∈ Dm K m F) (hw : hammingNorm v ≤ Lm Q m) :
    ∃ W W' : Codim2 K m, v ∈ Submodule.span F {incVec F W, incVec F W'} := by
  classical
  obtain ⟨W, W', hWW⟩ := h1 (Finset.univ.filter (fun x => v x ≠ 0)) hw
  refine ⟨W, W', ?_⟩
  have := base_change p _ _ hWW v hv (by intro x hx; simpa using hx)
  rwa [Set.image_pair, iota_incVec, iota_incVec] at this

theorem low_one
    (h2 : ∀ S : Finset (Lines K m), 3 * S.card ≤ 4 * em Q m →
      ∃ W : Codim2 K m, shorten (Um K m p) S ≤ Submodule.span (ZMod p) {incVec (ZMod p) W})
    (v : Lines K m → F) (hv : v ∈ Dm K m F) (hw : 3 * hammingNorm v ≤ 4 * em Q m) :
    ∃ W : Codim2 K m, v ∈ Submodule.span F {incVec F W} := by
  classical
  obtain ⟨W, hWW⟩ := h2 (Finset.univ.filter (fun x => v x ≠ 0)) hw
  refine ⟨W, ?_⟩
  have := base_change p _ _ hWW v hv (by intro x hx; simpa using hx)
  rwa [Set.image_singleton, iota_incVec] at this

theorem lower_bound
    (h1 : ∀ S : Finset (Lines K m), S.card ≤ Lm Q m →
      ∃ W W' : Codim2 K m, shorten (Um K m p) S ≤
        Submodule.span (ZMod p) {incVec (ZMod p) W, incVec (ZMod p) W'})
    (Ψ : (Lines K m → F) →ₗ[F] (Fin 2 → F))
    (hΨ1 : ∀ W : Codim2 K m, Ψ (incVec F W) ≠ 0)
    (hΨ2 : ∀ W W' : Codim2 K m, W ≠ W' →
        LinearIndependent F ![Ψ (incVec F W), Ψ (incVec F W')])
    (c : Lines K m → F) (hcD : c ∈ Dm K m F) (hcΨ : Ψ c = 0) (hc0 : c ≠ 0) :
    Lm Q m < hammingNorm c := by
  by_contra hle
  push Not at hle
  obtain ⟨W, W', hmem⟩ := low_two p Q h1 c hcD hle
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
  apply hc0
  by_cases hWW : W = W'
  · subst hWW
    have hc : c = (α + β) • incVec F W := by rw [← hαβ, add_smul]
    rw [hc, map_smul] at hcΨ
    rcases smul_eq_zero.mp hcΨ with h | h
    · rw [hc, h, zero_smul]
    · exact absurd h (hΨ1 W)
  · have hli := (LinearIndependent.pair_iff.mp (hΨ2 W W' hWW))
    have h0 : α • Ψ (incVec F W) + β • Ψ (incVec F W') = 0 := by
      rw [← map_smul, ← map_smul, ← map_add, hαβ, hcΨ]
    obtain ⟨ha, hb⟩ := hli α β h0
    rw [← hαβ, ha, hb]; simp

end main

end ProxGapTight.Dev.BaseCode3
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ProxGapTight.Dev.BaseCode4
open ProxGapTight ProxGapTight.Dev.BaseCode1 ProxGapTight.Dev.BaseCode2 ProxGapTight.Dev.BaseCode3

section aux
variable {K : Type} [Field K] [Fintype K] {m : ℕ} {F : Type} [Field F]

theorem incVec_of_le (W : Codim2 K m) (ℓ : Lines K m) (h : ℓ.1 ≤ W.1) : incVec F W ℓ = 1 := by
  unfold incVec; simp [h]

theorem incVec_of_not_le (W : Codim2 K m) (ℓ : Lines K m) (h : ¬ ℓ.1 ≤ W.1) :
    incVec F W ℓ = 0 := by
  unfold incVec; simp [h]

theorem exists_y [Fintype F] (hq : 3 ≤ Fintype.card F)
    (hN : Fintype.card (Codim2 K m) + 1 ≤ Fintype.card F) (s : Codim2 K m → (Fin 2 → F)) :
    ∃ y1 y2 : Fin 2 → F, y1 ≠ 0 ∧ y2 ≠ 0 ∧ (∀ (W : Codim2 K m) (l : F), l ≠ 0 → l • s W ≠ y1) ∧
      (∀ (W : Codim2 K m) (l : F), l ≠ 0 → l • s W ≠ y2) ∧ (∀ l : F, l • y1 ≠ y2) := by
  classical
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card F = r + 1 := ⟨Fintype.card F - 1, by omega⟩
  let B1 : Finset (Fin 2 → F) :=
    insert 0 (Finset.univ.image (fun pr : Codim2 K m × Fˣ => (pr.2 : F) • s pr.1))
  have hN' : Fintype.card (Codim2 K m) ≤ r := by omega
  have hB1 : B1.card ≤ 1 + Fintype.card (Codim2 K m) * r := by
    calc B1.card ≤ (Finset.univ.image (fun pr : Codim2 K m × Fˣ => (pr.2 : F) • s pr.1)).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ Fintype.card (Codim2 K m × Fˣ) + 1 := by
          have := Finset.card_image_le (s := (Finset.univ : Finset (Codim2 K m × Fˣ)))
            (f := fun pr : Codim2 K m × Fˣ => (pr.2 : F) • s pr.1)
          rw [Finset.card_univ] at this
          omega
      _ = 1 + Fintype.card (Codim2 K m) * r := by
          rw [Fintype.card_prod, Fintype.card_units, hr]; simp; ring
  have htot : Fintype.card (Fin 2 → F) = (r + 1) * (r + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, hr]; ring
  have hmul : Fintype.card (Codim2 K m) * r ≤ r * r := Nat.mul_le_mul_right r hN'
  have hr2 : 2 ≤ r := by omega
  have hex1 : ∃ y1, y1 ∉ B1 := by
    by_contra hc
    push Not at hc
    have : (Finset.univ : Finset (Fin 2 → F)) ⊆ B1 := fun y _ => hc y
    have := Finset.card_le_card this
    rw [Finset.card_univ, htot] at this
    nlinarith
  obtain ⟨y1, hy1⟩ := hex1
  let B2 : Finset (Fin 2 → F) := B1 ∪ Finset.univ.image (fun l : F => l • y1)
  have hB2 : B2.card ≤ B1.card + (r + 1) := by
    calc B2.card ≤ B1.card + (Finset.univ.image (fun l : F => l • y1)).card :=
          Finset.card_union_le _ _
      _ ≤ B1.card + (r + 1) := by
          have := Finset.card_image_le (s := (Finset.univ : Finset F)) (f := fun l : F => l • y1)
          rw [Finset.card_univ, hr] at this
          omega
  have hex2 : ∃ y2, y2 ∉ B2 := by
    by_contra hc
    push Not at hc
    have : (Finset.univ : Finset (Fin 2 → F)) ⊆ B2 := fun y _ => hc y
    have := Finset.card_le_card this
    rw [Finset.card_univ, htot] at this
    nlinarith
  obtain ⟨y2, hy2⟩ := hex2
  have hB1m : ∀ (W : Codim2 K m) (l : F), l ≠ 0 → l • s W ∈ B1 := by
    intro W l hl
    apply Finset.mem_insert_of_mem
    rw [Finset.mem_image]
    exact ⟨(W, Units.mk0 l hl), Finset.mem_univ _, rfl⟩
  have hy2B1 : y2 ∉ B1 := fun h => hy2 (Finset.mem_union_left _ h)
  refine ⟨y1, y2, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact hy1 (h ▸ Finset.mem_insert_self _ _)
  · intro h; exact hy2B1 (h ▸ Finset.mem_insert_self _ _)
  · intro W l hl h; exact hy1 (h ▸ hB1m W l hl)
  · intro W l hl h; exact hy2B1 (h ▸ hB1m W l hl)
  · intro l h
    exact hy2 (Finset.mem_union_right _ (by rw [Finset.mem_image]; exact ⟨l, Finset.mem_univ _, h⟩))

end aux

section main
variable (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [Fintype K] {m : ℕ} (Q : ℕ)
  {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

theorem exists_h (hm : 4 ≤ m) (hK : 2 < Fintype.card K) (hQK : Fintype.card K = Q)
    (Ψ : (Lines K m → F) →ₗ[F] (Fin 2 → F)) :
    ∃ h ∈ Dm K m F, Ψ h = 0 ∧ h ≠ 0 ∧ hammingNorm h < 3 * em Q m := by
  classical
  obtain ⟨W1, W2, W3, h12, h13, h23, ℓ0, l1, l2, l3⟩ := exists_three hm hK
  let W : Fin 3 → Codim2 K m := ![W1, W2, W3]
  let s : Fin 3 → (Fin 2 → F) := fun i => Ψ (incVec F (W i))
  have hnli : ¬ LinearIndependent F s := by
    intro hli
    have := hli.fintype_card_le_finrank
    simp at this
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnli
  let h : Lines K m → F := ∑ j, g j • incVec F (W j)
  have hD : h ∈ Dm K m F :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (incVec_mem_Dm (W j))
  have hΨ : Ψ h = 0 := by
    have : Ψ h = ∑ j, g j • s j := by simp [h, map_sum, s]
    rw [this]; exact hg
  have hsep : ∀ i : Fin 3, ∃ ℓ : Lines K m, ∀ j : Fin 3, (ℓ.1 ≤ (W j).1 ↔ j = i) := by
    intro i
    fin_cases i
    · obtain ⟨x, hx1, hx2, hx3⟩ := exists_vec_sep W1 W2 W3 h12 h13
      have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (zero_mem _)
      obtain ⟨ℓ, hℓ⟩ := line_of_vec x hx0
      refine ⟨ℓ, fun j => ?_⟩
      fin_cases j <;> simp [W, hℓ, hx1, hx2, hx3]
    · obtain ⟨x, hx1, hx2, hx3⟩ := exists_vec_sep W2 W1 W3 (Ne.symm h12) h23
      have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (zero_mem _)
      obtain ⟨ℓ, hℓ⟩ := line_of_vec x hx0
      refine ⟨ℓ, fun j => ?_⟩
      fin_cases j <;> simp [W, hℓ, hx1, hx2, hx3]
    · obtain ⟨x, hx1, hx2, hx3⟩ := exists_vec_sep W3 W1 W2 (Ne.symm h13) (Ne.symm h23)
      have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (zero_mem _)
      obtain ⟨ℓ, hℓ⟩ := line_of_vec x hx0
      refine ⟨ℓ, fun j => ?_⟩
      fin_cases j <;> simp [W, hℓ, hx1, hx2, hx3]
  have hh0 : h ≠ 0 := by
    obtain ⟨ℓ, hℓ⟩ := hsep i
    intro h0
    have : h ℓ = g i := by
      simp only [h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · rw [incVec_of_le _ _ ((hℓ i).mpr rfl), mul_one]
      · intro j _ hj
        rw [incVec_of_not_le _ _ (fun hle => hj ((hℓ j).mp hle)), mul_zero]
      · simp
    rw [h0] at this
    exact hi (by simpa using this.symm)
  refine ⟨h, hD, hΨ, hh0, ?_⟩
  -- weight
  let A : Fin 3 → Finset (Lines K m) := fun j => linesIn (W j).1
  have hA : ∀ j, (A j).card = em Q m := by
    intro j; simp only [A]; rw [card_linesIn_codim2, hQK]
  have hsub : ∀ ℓ, h ℓ ≠ 0 → ℓ ∈ (A 0 ∪ A 1) ∪ A 2 := by
    intro ℓ hℓ
    by_contra hnot
    apply hℓ
    simp only [h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j _
    rw [incVec_of_not_le _ _ (fun hle => hnot ?_), mul_zero]
    fin_cases j
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((mem_linesIn _ _).mpr hle))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((mem_linesIn _ _).mpr hle))
    · exact Finset.mem_union_right _ ((mem_linesIn _ _).mpr hle)
  have h1 := hammingNorm_le_of_subset h _ hsub
  have h2 := Finset.card_union_le (A 0 ∪ A 1) (A 2)
  have h3 := Finset.card_union_add_card_inter (A 0) (A 1)
  have h4 : 1 ≤ (A 0 ∩ A 1).card := by
    apply Finset.card_pos.mpr
    exact ⟨ℓ0, Finset.mem_inter.mpr ⟨(mem_linesIn _ _).mpr l1, (mem_linesIn _ _).mpr l2⟩⟩
  have e0 := hA 0
  have e1 := hA 1
  have e2 := hA 2
  omega

end main

end ProxGapTight.Dev.BaseCode4
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ProxGapTight.Dev.BaseCode
open ProxGapTight ProxGapTight.Dev.BaseCode1 ProxGapTight.Dev.BaseCode2 ProxGapTight.Dev.BaseCode3
  ProxGapTight.Dev.BaseCode4

theorem hd_sub {ι F : Type} [Field F] [DecidableEq F] [Fintype ι] (x y : ι → F) :
    hammingDist x y = hammingNorm (x - y) := by
  rw [hammingDist_comm, hammingDist_eq_hammingNorm, neg_add_eq_sub]

section main
variable (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [Fintype K] {m : ℕ} (Q : ℕ)
  {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

theorem main_X (hm : 4 ≤ m) (hK : 2 < Fintype.card K) (hQK : Fintype.card K = Q)
    (hF : Fintype.card F = Q ^ (2 * m))
    (h1 : ∀ S : Finset (Lines K m), S.card ≤ Lm Q m →
      ∃ W W' : Codim2 K m, shorten (Um K m p) S ≤
        Submodule.span (ZMod p) {incVec (ZMod p) W, incVec (ZMod p) W'})
    (h2 : ∀ S : Finset (Lines K m), 3 * S.card ≤ 4 * em Q m →
      ∃ W : Codim2 K m, shorten (Um K m p) S ≤ Submodule.span (ZMod p) {incVec (ZMod p) W})
    (Ψ : (Lines K m → F) →ₗ[F] (Fin 2 → F))
    (hΨ1 : ∀ W : Codim2 K m, Ψ (incVec F W) ≠ 0)
    (hΨ2 : ∀ W W' : Codim2 K m, W ≠ W' →
        LinearIndependent F ![Ψ (incVec F W), Ψ (incVec F W')]) :
    ∃ C : Submodule F (Lines K m → F), ∃ f g : Lines K m → F, C ≠ ⊥ ∧
      Lm Q m < minDist C ∧ minDist C < 3 * em Q m ∧
      (∀ c ∈ C, 4 * em Q m < 3 * hammingDist f c) ∧
      (∀ c ∈ C, 4 * em Q m < 3 * hammingDist g c) ∧
      ∃ T : Finset F, Q ^ (2 * (m - 2)) ≤ T.card ∧
        ∀ z ∈ T, ∃ c ∈ C, hammingDist (f + z • g) c ≤ em Q m := by
  classical
  let C : Submodule F (Lines K m → F) := Dm K m F ⊓ LinearMap.ker Ψ
  have hCmem : ∀ c, c ∈ C ↔ c ∈ Dm K m F ∧ Ψ c = 0 := fun c => by
    simp [C, Submodule.mem_inf]
  obtain ⟨h, hhD, hhΨ, hh0, hhw⟩ := exists_h Q hm hK hQK Ψ
  have hhC : h ∈ C := (hCmem h).mpr ⟨hhD, hhΨ⟩
  have hne : {w : ℕ | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = w}.Nonempty := ⟨_, h, hhC, hh0, rfl⟩
  have hLm : Lm Q m < minDist C := by
    obtain ⟨c, hcC, hc0, hcw⟩ := Nat.sInf_mem hne
    have := (hCmem c).mp hcC
    have hh := lower_bound p Q h1 Ψ hΨ1 hΨ2 c this.1 this.2 hc0
    unfold minDist
    rw [← hcw]; exact hh
  have hmin : minDist C < 3 * em Q m := by
    have : minDist C ≤ hammingNorm h := Nat.sInf_le ⟨h, hhC, hh0, rfl⟩
    omega
  have hCbot : C ≠ ⊥ := by
    intro hb
    rw [hb] at hhC
    exact hh0 (by simpa using hhC)
  -- counting
  have hN1 : Fintype.card (Codim2 K m) + 1 ≤ Fintype.card F := by
    have := card_codim2_add_one_le (K := K) (m := m)
    rw [hQK] at this; rw [hF]; exact this
  have hN2 : Q ^ (2 * (m - 2)) ≤ Fintype.card (Codim2 K m) := by
    have := card_codim2_ge (K := K) (m := m) (by omega)
    rwa [hQK] at this
  have hq : 3 ≤ Fintype.card F := by
    rw [hF]
    calc 3 ≤ Q := by omega
      _ ≤ Q ^ (2 * m) := Nat.le_self_pow (by omega) Q
  let s : Codim2 K m → (Fin 2 → F) := fun W => Ψ (incVec F W)
  obtain ⟨y1, y2, hy1, hy2, hP1, hP2, hP3⟩ := exists_y hq hN1 s
  have hli12 : LinearIndependent F ![y1, y2] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      simp only [zero_smul, add_zero] at hab
      rcases smul_eq_zero.mp hab with h | h
      · exact ⟨h, rfl⟩
      · exact absurd h hy1
    · exfalso
      have h3 : b • y2 = -(a • y1) := eq_neg_of_add_eq_zero_right hab
      apply hP3 (-(b⁻¹ * a))
      calc (-(b⁻¹ * a)) • y1 = b⁻¹ • (-(a • y1)) := by
            rw [smul_neg, neg_smul, smul_smul]
        _ = b⁻¹ • (b • y2) := by rw [h3]
        _ = y2 := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hdec : ∀ W : Codim2 K m, ∃ a b : F, s W = a • y1 + b • y2 :=
    fun W => pair_span y1 y2 hli12 (s W)
  choose a b hab using hdec
  have ha0 : ∀ W, a W ≠ 0 := by
    intro W ha
    have hb : b W ≠ 0 := by
      intro hb
      have := hΨ1 W
      apply this
      show s W = 0
      rw [hab W, ha, hb]; simp
    apply hP2 W (b W)⁻¹ (inv_ne_zero hb)
    rw [hab W, ha, zero_smul, zero_add, smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hb0 : ∀ W, b W ≠ 0 := by
    intro W hb
    have ha := ha0 W
    apply hP1 W (a W)⁻¹ (inv_ne_zero ha)
    rw [hab W, hb, zero_smul, add_zero, smul_smul, inv_mul_cancel₀ ha, one_smul]
  let α : Codim2 K m → F := fun W => (a W)⁻¹
  let β : Codim2 K m → F := fun W => (a W)⁻¹ * b W
  have hα0 : ∀ W, α W ≠ 0 := fun W => inv_ne_zero (ha0 W)
  have hαs : ∀ W, α W • s W = y1 + β W • y2 := by
    intro W
    simp only [α, β]
    rw [hab W, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ (ha0 W), one_smul]
  -- f and g
  obtain ⟨W1, W2, W3, h12, -, -, -⟩ := exists_three (K := K) hm hK
  have hli := hΨ2 W1 W2 h12
  have mkfg : ∀ y : Fin 2 → F, ∃ x ∈ Dm K m F, Ψ x = y := by
    intro y
    obtain ⟨u1, u2, hu⟩ := pair_span _ _ hli y
    refine ⟨u1 • incVec F W1 + u2 • incVec F W2,
      Submodule.add_mem _ (Submodule.smul_mem _ _ (incVec_mem_Dm W1))
        (Submodule.smul_mem _ _ (incVec_mem_Dm W2)), ?_⟩
    rw [map_add, map_smul, map_smul]
    exact hu.symm
  obtain ⟨f, hfD, hfΨ⟩ := mkfg y1
  obtain ⟨g, hgD, hgΨ⟩ := mkfg y2
  have dist : ∀ y : Fin 2 → F, y ≠ 0 → (∀ (W : Codim2 K m) (l : F), l ≠ 0 → l • s W ≠ y) →
      ∀ x ∈ Dm K m F, Ψ x = y → ∀ c ∈ C, 4 * em Q m < 3 * hammingDist x c := by
    intro y hy hP x hx hxΨ c hc
    have hc' := (hCmem c).mp hc
    by_contra hle
    push Not at hle
    rw [hd_sub] at hle
    have hv : x - c ∈ Dm K m F := Submodule.sub_mem _ hx hc'.1
    obtain ⟨W, hW⟩ := low_one p Q h2 (x - c) hv hle
    obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp hW
    have hΨv : Ψ (x - c) = y := by rw [map_sub, hxΨ, hc'.2, sub_zero]
    rw [← hl, map_smul] at hΨv
    have hl0 : l ≠ 0 := by
      rintro rfl
      apply hy
      rw [← hΨv]; simp
    exact hP W l hl0 hΨv
  refine ⟨C, f, g, hCbot, hLm, hmin, dist y1 hy1 hP1 f hfD hfΨ, dist y2 hy2 hP2 g hgD hgΨ, ?_⟩
  -- exceptional coefficients
  have hβinj : Function.Injective β := by
    intro W W' hWW
    by_contra hne
    have hli' := LinearIndependent.pair_iff.mp (hΨ2 W W' hne)
    have h0 : α W • s W + (-α W') • s W' = 0 := by
      rw [hαs W, neg_smul, hαs W', hWW]; simp
    exact hα0 W (hli' _ _ h0).1
  refine ⟨Finset.univ.image β, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hβinj, Finset.card_univ]; exact hN2
  · intro z hz
    obtain ⟨W, -, rfl⟩ := Finset.mem_image.mp hz
    have hu : α W • incVec F W ∈ Dm K m F := Submodule.smul_mem _ _ (incVec_mem_Dm W)
    have hcC : f + β W • g - α W • incVec F W ∈ C := by
      rw [hCmem]
      refine ⟨Submodule.sub_mem _ (Submodule.add_mem _ hfD (Submodule.smul_mem _ _ hgD)) hu, ?_⟩
      have : Ψ (α W • incVec F W) = y1 + β W • y2 := by
        rw [map_smul]; exact hαs W
      rw [map_sub, map_add, map_smul, hfΨ, hgΨ, this]; simp
    refine ⟨_, hcC, ?_⟩
    rw [hd_sub, sub_sub_cancel]
    have := hammingNorm_le_of_subset (α W • incVec F W) (linesIn W.1) (by
      intro ℓ hℓ
      rw [mem_linesIn]
      by_contra hn
      apply hℓ
      simp [incVec_of_not_le _ _ hn])
    rw [card_linesIn_codim2, hQK] at this
    exact this

end main

end ProxGapTight.Dev.BaseCode

namespace ProxGapTight

theorem chk_lemma_3_2_base_code (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) :
    ∃ cQ : ℝ, 0 < cQ ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], Fintype.card F = (p ^ a) ^ (2 * m) →
        ∃ C : Submodule F (Fin (nm (p ^ a) m) → F), ∃ f g : Fin (nm (p ^ a) m) → F,
          C ≠ ⊥ ∧
          (Lm (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ) < relDist C ∧
          relDist C < 3 * (em (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ) ∧
          4 * (em (p ^ a) m : ℝ) / (3 * (nm (p ^ a) m : ℝ)) < distToCode f C ∧
          4 * (em (p ^ a) m : ℝ) / (3 * (nm (p ^ a) m : ℝ)) < distToCode g C ∧
          cQ * (((p ^ a) ^ (2 * m) : ℕ) : ℝ) ≤
            ((exceptionalSet ((em (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ)) f g C).card : ℝ) := by
  open ProxGapTight.Dev.BaseCode ProxGapTight.Dev.BaseCode1 ProxGapTight.Dev.BaseCode2 in
  obtain ⟨m₀, hm₀⟩ := lemma_3_4_shortenings p a hQ h49 h121
  have hQpos : (0 : ℝ) < ((p ^ a : ℕ) : ℝ) := by positivity
  refine ⟨1 / ((p ^ a : ℕ) : ℝ) ^ 4, by positivity, max m₀ 4, ?_⟩
  intro m hm F _ _ _ hF
  have hm4 : 4 ≤ m := le_trans (le_max_right _ _) hm
  have hmm0 : m₀ ≤ m := le_trans (le_max_left _ _) hm
  have ha : a ≠ 0 := by rintro rfl; simp at hQ
  letI : Fintype (GaloisField p a) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField p a) = p ^ a := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p a ha
  obtain ⟨h1, h2, -⟩ := hm₀ m hmm0 (GaloisField p a) hK
  -- characteristic
  obtain ⟨p', hp'⟩ := CharP.exists F
  obtain ⟨n, hpr, hcard⟩ := FiniteField.card F p'
  have hdvd : p' ∣ p ^ (a * (2 * m)) := by
    have : p' ∣ Fintype.card F := by
      rw [hcard]; exact dvd_pow_self p' (by exact n.pos.ne')
    rwa [hF, ← pow_mul] at this
  have hpp : p' = p :=
    (Nat.prime_dvd_prime_iff_eq hpr Fact.out).mp (hpr.dvd_of_dvd_pow hdvd)
  subst hpp
  letI : Algebra (ZMod p') F := ZMod.algebra F p'
  obtain ⟨Ψ, hΨ1, hΨ2⟩ := lemma_3_5_syndromes p' a m hm4 (GaloisField p' a) hK F hF
  have hF' : Fintype.card F = (p' ^ a) ^ (2 * m) := hF
  obtain ⟨C, f, g, hCbot, hLm, hmin, hdf, hdg, T, hT, hTmem⟩ :=
    ProxGapTight.Dev.BaseCode.main_X p' (p' ^ a) (K := GaloisField p' a) hm4
      (by omega) hK hF' h1 h2 Ψ hΨ1 hΨ2

  have hcard : Fintype.card (Lines (GaloisField p' a) m) = nm (p' ^ a) m := by
    rw [card_lines, hK]
  let σ : Fin (nm (p' ^ a) m) ≃ Lines (GaloisField p' a) m :=
    (Fintype.equivFinOfCardEq hcard).symm
  have hn : 0 < nm (p' ^ a) m := by
    obtain ⟨c, -, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCbot
    obtain ⟨x, -⟩ := Function.ne_iff.mp hc0
    rw [← hcard]
    exact Fintype.card_pos_iff.mpr ⟨x⟩
  have hnR : (0 : ℝ) < (nm (p' ^ a) m : ℝ) := by exact_mod_cast hn
  have key : ∀ x : Lines (GaloisField p' a) m → F, (∀ c ∈ C, 4 * em (p' ^ a) m < 3 * hammingDist x c) →
      4 * (em (p' ^ a) m : ℝ) / (3 * (nm (p' ^ a) m : ℝ)) < distToCode x C := by
    intro x hx
    have hne : {w : ℕ | ∃ c ∈ C, hammingDist x c = w}.Nonempty := ⟨_, 0, C.zero_mem, rfl⟩
    obtain ⟨c, hc, hcw⟩ := Nat.sInf_mem hne
    have h3 := hx c hc
    rw [hcw] at h3
    unfold distToCode
    rw [hcard, div_lt_div_iff₀ (by positivity) hnR]
    have : (4 * em (p' ^ a) m : ℝ) < 3 * (sInf {w : ℕ | ∃ c ∈ C, hammingDist x c = w} : ℕ) := by
      exact_mod_cast h3
    nlinarith
  refine ⟨C.map (ProxGapTight.Dev.BaseCode2.reidx F σ).toLinearMap,
    ProxGapTight.Dev.BaseCode2.reidx F σ f, ProxGapTight.Dev.BaseCode2.reidx F σ g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hb
    apply hCbot
    have := Submodule.map_injective_of_injective (ProxGapTight.Dev.BaseCode2.reidx F σ).injective
      (hb.trans (Submodule.map_bot _).symm)
    exact this
  · unfold relDist
    rw [ProxGapTight.Dev.BaseCode2.minDist_map, Fintype.card_fin]
    exact div_lt_div_of_pos_right (by exact_mod_cast hLm) hnR
  · unfold relDist
    rw [ProxGapTight.Dev.BaseCode2.minDist_map, Fintype.card_fin]
    refine div_lt_div_of_pos_right ?_ hnR
    have : (minDist C : ℝ) < ((3 * em (p' ^ a) m : ℕ) : ℝ) := by exact_mod_cast hmin
    simpa using this
  · rw [ProxGapTight.Dev.BaseCode2.distToCode_map]; exact key f hdf
  · rw [ProxGapTight.Dev.BaseCode2.distToCode_map]; exact key g hdg
  · have hsub : T ⊆ exceptionalSet ((em (p' ^ a) m : ℝ) / (nm (p' ^ a) m : ℝ))
        (ProxGapTight.Dev.BaseCode2.reidx F σ f) (ProxGapTight.Dev.BaseCode2.reidx F σ g)
        (C.map (ProxGapTight.Dev.BaseCode2.reidx F σ).toLinearMap) := by
      intro z hz
      unfold exceptionalSet
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have heq : ProxGapTight.Dev.BaseCode2.reidx F σ f + z • ProxGapTight.Dev.BaseCode2.reidx F σ g
          = ProxGapTight.Dev.BaseCode2.reidx F σ (f + z • g) := by
        simp
      rw [heq, ProxGapTight.Dev.BaseCode2.distToCode_map]
      obtain ⟨c, hc, hcz⟩ := hTmem z hz
      have hle : sInf {w : ℕ | ∃ c ∈ C, hammingDist (f + z • g) c = w} ≤ em (p' ^ a) m :=
        le_trans (Nat.sInf_le ⟨c, hc, rfl⟩) hcz
      unfold distToCode
      rw [hcard]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hnR.le
    have h5 := Finset.card_le_card hsub
    have hcQ : (1 / ((p' ^ a : ℕ) : ℝ) ^ 4) * (((p' ^ a) ^ (2 * m) : ℕ) : ℝ)
        = ((p' ^ a) ^ (2 * (m - 2)) : ℕ) := by
      have h2m : 2 * m = 2 * (m - 2) + 4 := by omega
      rw [h2m]
      push_cast
      rw [pow_add]
      field_simp
      exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by exact_mod_cast (Fact.out : p'.Prime).ne_zero))
    rw [hcQ]
    exact_mod_cast hT.trans h5

end ProxGapTight
end

theorem solution : type_of% @ProxGapTight.chk_lemma_3_2_base_code := @ProxGapTight.chk_lemma_3_2_base_code
