-- Prove2me | solution 1 for ProxGapTight.theorem_1_1_johnson_tight
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:25:31.767296+00:00
-- url     : https://prove2.me/submissions/3318848a-794f-48c2-85d0-6cae13f3e9ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ProxGapTight_nm
import Definitions.Def_ProxGapTight_em
import Definitions.Def_ProxGapTight_Lm
import Definitions.Def_ProxGapTight_Lines
import Definitions.Def_ProxGapTight_Codim2
import Definitions.Def_ProxGapTight_Um
import Definitions.Def_ProxGapTight_shorten
import Definitions.Def_ProxGapTight_minDist
import Definitions.Def_ProxGapTight_relDist
import Definitions.Def_ProxGapTight_distToCode
import Definitions.Def_ProxGapTight_exceptionalSet
import Definitions.Def_ProxGapTight_incVec
import Theorems.Thm_ProxGapTight_lemma_3_4_shortenings
import Theorems.Thm_ProxGapTight_lemma_3_5_syndromes
import Theorems.Thm_ProxGapTight_dim_Um_le
import Theorems.Thm_ProxGapTight_supercode_prob
import Definitions.Def_ProxGapTight_rate
import Definitions.Def_ProxGapTight_Phi
import Definitions.Def_ProxGapTight_amp
import Theorems.Thm_ProxGapTight_amp_chernoff
import Definitions.Def_ProxGapTight_J32
import Definitions.Def_ProxGapTight_Gam
import Theorems.Thm_ProxGapTight_parameter_choice
import Theorems.Thm_ProxGapTight_thresholds_ordered

section
set_option autoImplicit false

/-!
Interface between the two halves of the proof of `theorem_1_1_johnson_tight` (q320).
`base_data` (the paper's Lemma 3.2 plus the subfield trick, with the extra facts the union bound needs:
`C ⊆ D`, `f, g ∈ D`, `D` of bounded size) is proved by one prover (file `BaseData.lean`);
`Main.lean` proves the goal from it.  Both must state it EXACTLY as here.
Words over a finite `F`-module `E`; `dE`, `minD` are the distance notions of the paper for such words.
-/

namespace ProxGapTight.Dev.Main

/-- distance of `x` to the `F`-submodule `C` of `Fin n → E`, in Hamming weight (a natural number). -/
noncomputable def dE {F E : Type} [Field F] [AddCommGroup E] [Module F E] [DecidableEq E] (n : ℕ)
    (x : Fin n → E) (C : Submodule F (Fin n → E)) : ℕ :=
  sInf {w : ℕ | ∃ c ∈ C, hammingNorm (x - c) = w}

/-- minimum weight of a nonzero word of `C`. -/
noncomputable def minD {F E : Type} [Field F] [AddCommGroup E] [Module F E] [DecidableEq E] (n : ℕ)
    (C : Submodule F (Fin n → E)) : ℕ :=
  sInf {w : ℕ | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = w}

end ProxGapTight.Dev.Main
end

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

end main

end ProxGapTight.Dev.BaseCode

namespace ProxGapTight

end ProxGapTight
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ProxGapTight.Dev.BaseData
open ProxGapTight ProxGapTight.Dev.BaseCode ProxGapTight.Dev.BaseCode1 ProxGapTight.Dev.BaseCode2 ProxGapTight.Dev.BaseCode3
  ProxGapTight.Dev.BaseCode4

section main
variable (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [Fintype K] {m : ℕ} (Q : ℕ)
  {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

theorem main_X' (hm : 4 ≤ m) (hK : 2 < Fintype.card K) (hQK : Fintype.card K = Q)
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
      C ≤ Dm K m F ∧ f ∈ Dm K m F ∧ g ∈ Dm K m F ∧
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
  refine ⟨C, f, g, hCbot, hLm, hmin, dist y1 hy1 hP1 f hfD hfΨ, dist y2 hy2 hP2 g hgD hgΨ,
    inf_le_left, hfD, hgD, ?_⟩
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
section dim
variable (p : ℕ) [Fact p.Prime]

theorem finrank_Dm_le (a m : ℕ) (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = p ^ a)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] :
    Module.finrank E (Dm K m E) ≤
      Nat.choose (a * m + 2 * a * (p - 1)) (2 * a * (p - 1)) := by
  classical
  have hdim := ProxGapTight.dim_Um_le p a m K hK
  let U := Um K m p
  let b := Module.finBasis (ZMod p) U
  let v : Fin (Module.finrank (ZMod p) U) → (Lines K m → ZMod p) := fun i => (b i : _)
  have hspan : Submodule.span (ZMod p) (Set.range v) = U := by
    have h1 := congrArg (Submodule.map U.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h1
    have hr : Set.range v = U.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [hr]; exact h1
  have hle : Dm K m E ≤ Submodule.span E (Set.range fun i => iota p K m E (v i)) := by
    unfold Dm
    rw [Submodule.span_le]
    rintro _ ⟨W, rfl⟩
    show incVec E W ∈ _
    rw [← iota_incVec p (F := E) W]
    have hW : incVec (ZMod p) W ∈ Submodule.span (ZMod p) (Set.range v) := by
      rw [hspan]; exact Submodule.subset_span ⟨W, rfl⟩
    have := iota_mem_span p (F := E) (Set.range v) _ hW
    rwa [← Set.range_comp] at this
  calc Module.finrank E (Dm K m E)
      ≤ Module.finrank E (Submodule.span E (Set.range fun i => iota p K m E (v i))) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank (ZMod p) U)) := finrank_range_le_card _
    _ = Module.finrank (ZMod p) U := Fintype.card_fin _
    _ ≤ _ := hdim

end dim

section pigeon
variable {F E : Type} [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E]
  [Algebra F E]

theorem pigeon (TE : Finset E) :
    ∃ b : E, b ≠ 0 ∧ (Fintype.card F - 1) * (TE.card - 1) ≤
      (Fintype.card E - 1) *
        (Finset.univ.filter (fun z : F => z ≠ 0 ∧ algebraMap F E z * b ∈ TE)).card := by
  classical
  set T' := TE.erase 0 with hT'
  have hcount : ∑ b ∈ (Finset.univ.erase (0 : E)),
      (Finset.univ.filter (fun z : F => z ≠ 0 ∧ algebraMap F E z * b ∈ TE)).card
      = (Fintype.card F - 1) * T'.card := by
    have h1 : ∀ b : E, (Finset.univ.filter (fun z : F => z ≠ 0 ∧ algebraMap F E z * b ∈ TE)).card
        = ∑ z : F, if (z ≠ 0 ∧ algebraMap F E z * b ∈ TE) then 1 else 0 := by
      intro b
      rw [Finset.card_filter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ z : F, ∑ b ∈ (Finset.univ.erase (0 : E)),
        (if (z ≠ 0 ∧ algebraMap F E z * b ∈ TE) then 1 else 0)
        = if z ≠ 0 then T'.card else 0 := by
      intro z
      by_cases hz : z = 0
      · simp [hz]
      · simp only [ne_eq, hz, not_false_eq_true, true_and, if_true]
        rw [← Finset.card_filter]
        refine Finset.card_bij (fun b _ => algebraMap F E z * b) ?_ ?_ ?_
        · intro b hb
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at hb
          simp only [hT', Finset.mem_erase, ne_eq]
          refine ⟨mul_ne_zero ?_ hb.1, hb.2⟩
          simpa using hz
        · intro b _ b' _ h
          have hz' : algebraMap F E z ≠ 0 := by simpa using hz
          exact mul_left_cancel₀ hz' h
        · intro t ht
          simp only [hT', Finset.mem_erase, ne_eq] at ht
          have hz' : algebraMap F E z ≠ 0 := by simpa using hz
          refine ⟨(algebraMap F E z)⁻¹ * t, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
            refine ⟨mul_ne_zero (inv_ne_zero hz') ht.1, ?_⟩
            rw [mul_inv_cancel_left₀ hz']; exact ht.2
          · exact mul_inv_cancel_left₀ hz' t
    simp_rw [h2]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [show (Finset.univ.filter (fun z : F => z ≠ 0)) = Finset.univ.erase 0 by
      ext z; simp, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  by_contra hcon
  push Not at hcon
  have hne : (Finset.univ.erase (0 : E)).Nonempty := by
    have : 1 < Fintype.card E := Fintype.one_lt_card
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  have hlt := Finset.sum_lt_sum_of_nonempty hne (f := fun b =>
      (Fintype.card E - 1) * (Finset.univ.filter (fun z : F => z ≠ 0 ∧ algebraMap F E z * b ∈ TE)).card)
    (g := fun _ => (Fintype.card F - 1) * (TE.card - 1)) (by
      intro b hb
      have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
      have := hcon b hb0
      omega)
  rw [← Finset.mul_sum, hcount, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, smul_eq_mul] at hlt
  have h3 : TE.card - 1 ≤ T'.card := Finset.pred_card_le_card_erase
  have h4 : (Fintype.card F - 1) * (TE.card - 1) ≤ (Fintype.card F - 1) * T'.card :=
    Nat.mul_le_mul_left _ h3
  have h5 := Nat.mul_le_mul_left (Fintype.card E - 1) h4
  nlinarith

end pigeon

section core
open ProxGapTight.Dev.Main

theorem core (p a : ℕ) [Fact p.Prime] (m : ℕ) (hm4 : 4 ≤ m) (K : Type) [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) (hQ : 2 < p ^ a)
    (h1 : ∀ S : Finset (Lines K m), S.card ≤ Lm (p ^ a) m →
      ∃ W W' : Codim2 K m, shorten (Um K m p) S ≤
        Submodule.span (ZMod p) {incVec (ZMod p) W, incVec (ZMod p) W'})
    (h2 : ∀ S : Finset (Lines K m), 3 * S.card ≤ 4 * em (p ^ a) m →
      ∃ W : Codim2 K m, shorten (Um K m p) S ≤ Submodule.span (ZMod p) {incVec (ZMod p) W})
    (F E : Type) [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod p) E] [Algebra F E]
    (hE : Fintype.card E = (p ^ a) ^ (2 * m)) (hF2 : 2 ≤ Fintype.card F) :
    ∃ (Cm D : Submodule F (Fin (nm (p ^ a) m) → E)) (fm gm : Fin (nm (p ^ a) m) → E)
        (T : Finset F),
        Cm ≠ ⊥ ∧ Cm ≤ D ∧ fm ∈ D ∧ gm ∈ D ∧
        Nat.card D ≤ (Fintype.card E) ^ (Nat.choose (a * m + 2 * a * (p - 1)) (2 * a * (p - 1))) ∧
        (Lm (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ) < (minD (nm (p ^ a) m) Cm : ℝ) / (nm (p ^ a) m : ℝ) ∧
        (minD (nm (p ^ a) m) Cm : ℝ) / (nm (p ^ a) m : ℝ) < 3 * (em (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ) ∧
        4 * (em (p ^ a) m : ℝ) / (3 * (nm (p ^ a) m : ℝ)) <
          (dE (nm (p ^ a) m) fm Cm : ℝ) / (nm (p ^ a) m : ℝ) ∧
        4 * (em (p ^ a) m : ℝ) / (3 * (nm (p ^ a) m : ℝ)) <
          (dE (nm (p ^ a) m) gm Cm : ℝ) / (nm (p ^ a) m : ℝ) ∧
        1 / (4 * ((p ^ a : ℕ) : ℝ) ^ 4) * (Fintype.card F : ℝ) ≤ (T.card : ℝ) ∧
        ∀ z ∈ T, (dE (nm (p ^ a) m) (fm + z • gm) Cm : ℝ) / (nm (p ^ a) m : ℝ) ≤
          (em (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ) := by
  classical
  obtain ⟨Ψ, hΨ1, hΨ2⟩ := lemma_3_5_syndromes p a m hm4 K hK E hE
  obtain ⟨C, f, g, hCbot, hLm, hmin, hdf, hdg, hCD, hfD, hgD, TE, hTE, hTEmem⟩ :=
    main_X' p (p ^ a) (K := K) hm4 (by omega) hK hE h1 h2 Ψ hΨ1 hΨ2
  obtain ⟨b, hb0, hpig⟩ := pigeon (F := F) (E := E) TE
  have hcard : Fintype.card (Lines K m) = nm (p ^ a) m := by
    rw [card_lines, hK]
  let σ : Fin (nm (p ^ a) m) ≃ Lines K m := (Fintype.equivFinOfCardEq hcard).symm
  have hn : 0 < nm (p ^ a) m := by
    obtain ⟨c, -, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCbot
    obtain ⟨x, -⟩ := Function.ne_iff.mp hc0
    rw [← hcard]
    exact Fintype.card_pos_iff.mpr ⟨x⟩
  have hnR : (0 : ℝ) < (nm (p ^ a) m : ℝ) := by exact_mod_cast hn
  let R := reidx E σ
  have hR : ∀ x, R x = x ∘ σ := fun x => rfl
  let Cm : Submodule F (Fin (nm (p ^ a) m) → E) :=
    (C.map R.toLinearMap).restrictScalars F
  let D : Submodule F (Fin (nm (p ^ a) m) → E) :=
    ((Dm K m E).map R.toLinearMap).restrictScalars F
  have hmemC : ∀ x, x ∈ Cm ↔ ∃ c ∈ C, R c = x := fun x => Iff.rfl
  have hnorm : ∀ x c : Lines K m → E, hammingNorm (R x - R c) = hammingNorm (x - c) := by
    intro x c
    rw [← map_sub, hR]; exact hammingNorm_comp_equiv σ _
  have dE_gt : ∀ (x : Fin (nm (p ^ a) m) → E) (B : ℕ),
      (∀ c ∈ Cm, B < hammingNorm (x - c)) → B < dE (nm (p ^ a) m) x Cm := by
    intro x B hx
    have hne : {w : ℕ | ∃ c ∈ Cm, hammingNorm (x - c) = w}.Nonempty := ⟨_, 0, Cm.zero_mem, rfl⟩
    obtain ⟨c, hc, hcw⟩ := Nat.sInf_mem hne
    unfold dE
    rw [← hcw]; exact hx c hc
  have dE_le : ∀ (x c : Fin (nm (p ^ a) m) → E) (B : ℕ), c ∈ Cm → hammingNorm (x - c) ≤ B →
      dE (nm (p ^ a) m) x Cm ≤ B := fun x c B hc hB =>
    le_trans (Nat.sInf_le ⟨c, hc, rfl⟩) hB
  have key : ∀ (x : Lines K m → E), (∀ c ∈ C, 4 * em (p ^ a) m < 3 * hammingDist x c) →
      4 * (em (p ^ a) m : ℝ) / (3 * (nm (p ^ a) m : ℝ)) <
        (dE (nm (p ^ a) m) (R x) Cm : ℝ) / (nm (p ^ a) m : ℝ) := by
    intro x hx
    have h3 : 4 * em (p ^ a) m < 3 * dE (nm (p ^ a) m) (R x) Cm := by
      by_contra hcon
      push Not at hcon
      have hne : {w : ℕ | ∃ c ∈ Cm, hammingNorm (R x - c) = w}.Nonempty :=
        ⟨_, 0, Cm.zero_mem, rfl⟩
      obtain ⟨c, hc, hcw⟩ := Nat.sInf_mem hne
      obtain ⟨c', hc', rfl⟩ := (hmemC c).mp hc
      have := hx c' hc'
      rw [hd_sub, ← hnorm] at this
      have h4 : dE (nm (p ^ a) m) (R x) Cm = hammingNorm (R x - R c') := hcw.symm
      omega
    rw [div_lt_div_iff₀ (by positivity) hnR]
    have : (4 * em (p ^ a) m : ℝ) < 3 * (dE (nm (p ^ a) m) (R x) Cm : ℕ) := by
      exact_mod_cast h3
    nlinarith
  have hbu : IsUnit b := Ne.isUnit hb0
  have hgb : ∀ c ∈ C, 4 * em (p ^ a) m < 3 * hammingDist (b • g) c := by
    intro c hc
    have := hdg (b⁻¹ • c) (Submodule.smul_mem _ _ hc)
    rw [hd_sub] at this ⊢
    have e : b • g - c = b • (g - b⁻¹ • c) := by
      rw [smul_sub, smul_inv_smul₀ hb0]
    rw [e, hammingNorm_smul (fun i => (hbu.isSMulRegular E))]
    exact this
  refine ⟨Cm, D, R f, R (b • g), Finset.univ.filter (fun z : F => z ≠ 0 ∧ algebraMap F E z * b ∈ TE),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, key f hdf, key (b • g) hgb, ?_, ?_⟩
  · intro hb
    apply hCbot
    have hb' : C.map R.toLinearMap = ⊥ := by
      ext x; constructor
      · intro hx
        have hx' : x ∈ Cm := hx
        rw [hb, Submodule.mem_bot] at hx'
        rw [Submodule.mem_bot]; exact hx'
      · intro hx; rw [Submodule.mem_bot] at hx; rw [hx]; exact Submodule.zero_mem _
    exact Submodule.map_injective_of_injective R.injective (hb'.trans (Submodule.map_bot _).symm)
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := (hmemC x).mp hx
    exact ⟨c, hCD hc, rfl⟩
  · exact ⟨f, hfD, rfl⟩
  · exact ⟨b • g, Submodule.smul_mem _ _ hgD, rfl⟩
  · have e0 : Nat.card D = Nat.card ((Dm K m E).map R.toLinearMap) := rfl
    have e1 : Nat.card ((Dm K m E).map R.toLinearMap) = Nat.card (Dm K m E) :=
      (Nat.card_congr (Submodule.equivMapOfInjective R.toLinearMap R.injective (Dm K m E)).toEquiv).symm
    rw [e0, e1, Module.natCard_eq_pow_finrank (K := E), Nat.card_eq_fintype_card]
    exact Nat.pow_le_pow_right Fintype.card_pos (finrank_Dm_le p a m K hK E)
  · have : minD (nm (p ^ a) m) Cm = minDist (C.map R.toLinearMap) := rfl
    rw [this, minDist_map]
    exact div_lt_div_of_pos_right (by exact_mod_cast hLm) hnR
  · have : minD (nm (p ^ a) m) Cm = minDist (C.map R.toLinearMap) := rfl
    rw [this, minDist_map]
    refine div_lt_div_of_pos_right ?_ hnR
    have : (minDist C : ℝ) < ((3 * em (p ^ a) m : ℕ) : ℝ) := by exact_mod_cast hmin
    simpa using this
  · -- counting
    set t := (Finset.univ.filter (fun z : F => z ≠ 0 ∧ algebraMap F E z * b ∈ TE)).card with ht
    have hQ4 : (p ^ a) ^ 4 ≤ (p ^ a) ^ (2 * (m - 2)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hx2 : 2 ≤ (p ^ a) ^ (2 * (m - 2)) := by
      have : 2 ≤ (p ^ a) ^ 4 := le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
      omega
    have hX : Fintype.card E = (p ^ a) ^ (2 * (m - 2)) * (p ^ a) ^ 4 := by
      rw [hE, ← pow_add]; congr 1; omega
    have hTE2 : 2 ≤ TE.card := le_trans hx2 hTE
    have hR : ((Fintype.card F : ℝ) - 1) * ((TE.card : ℝ) - 1) ≤ ((Fintype.card E : ℝ) - 1) * t := by
      have h0 : 1 ≤ Fintype.card F := by omega
      have h0' : 1 ≤ Fintype.card E := Fintype.card_pos
      have := (Nat.cast_le (α := ℝ)).mpr hpig
      rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h0, Nat.cast_sub (by omega : 1 ≤ TE.card),
        Nat.cast_sub h0', Nat.cast_one] at this
    have hxR : (2 : ℝ) ≤ (((p ^ a) ^ (2 * (m - 2)) : ℕ) : ℝ) := by exact_mod_cast hx2
    have hTER : (((p ^ a) ^ (2 * (m - 2)) : ℕ) : ℝ) ≤ (TE.card : ℝ) := by exact_mod_cast hTE
    have hFR : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hF2
    have hXR : (Fintype.card E : ℝ) = (((p ^ a) ^ (2 * (m - 2)) : ℕ) : ℝ) * ((p ^ a : ℕ) : ℝ) ^ 4 := by
      rw [hX]; push_cast; ring
    set x : ℝ := (((p ^ a) ^ (2 * (m - 2)) : ℕ) : ℝ) with hxdef
    set Qr : ℝ := ((p ^ a : ℕ) : ℝ) with hQr
    have hQpos : 0 < Qr := by
      have : (2:ℝ) < Qr := by rw [hQr]; exact_mod_cast hQ
      linarith
    have hA : (Fintype.card F : ℝ) * x ≤ 4 * (((Fintype.card F : ℝ) - 1) * ((TE.card : ℝ) - 1)) := by
      have h1' : (Fintype.card F : ℝ) / 2 ≤ (Fintype.card F : ℝ) - 1 := by linarith
      have h2' : x / 2 ≤ (TE.card : ℝ) - 1 := by linarith
      have := mul_le_mul h1' h2' (by linarith) (by linarith)
      nlinarith
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have hB : (((Fintype.card E : ℝ) - 1) * t) ≤ (Fintype.card E : ℝ) * t := by nlinarith
    have hC : (Fintype.card F : ℝ) * x ≤ 4 * (x * Qr ^ 4 * t) := by
      rw [← hXR]; nlinarith
    have hC' : (Fintype.card F : ℝ) ≤ 4 * Qr ^ 4 * t := by
      have hxpos : 0 < x := by linarith
      by_contra hcon
      push Not at hcon
      nlinarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨c, hc, hcz⟩ := hTEmem _ hz.2
    have heq : R f + z • R (b • g) = R (f + (algebraMap F E z * b) • g) := by
      have e2 : z • R (b • g) = R ((algebraMap F E z * b) • g) := by
        rw [← algebraMap_smul E z (R (b • g)), ← map_smul, smul_smul]
      rw [map_add, e2]
    have hle : dE (nm (p ^ a) m) (R f + z • R (b • g)) Cm ≤ em (p ^ a) m := by
      refine dE_le _ (R c) _ ((hmemC _).mpr ⟨c, hc, rfl⟩) ?_
      rw [heq, hnorm, ← hd_sub]; exact hcz
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hnR.le

end core

end ProxGapTight.Dev.BaseData

namespace ProxGapTight.Dev.Main
open ProxGapTight ProxGapTight.Dev.BaseData

theorem base_data_proof (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a) (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121)
    (m₁ : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ s₁ : ℕ, ∀ s : ℕ, s₁ ≤ s → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
      Fintype.card F = p ^ s →
      ∃ (E : Type) (_ : Field E) (_ : Fintype E) (_ : DecidableEq E) (_ : Algebra F E)
        (m r : ℕ) (Cm D : Submodule F (Fin (nm (p ^ a) m) → E)) (fm gm : Fin (nm (p ^ a) m) → E)
        (T : Finset F),
        m₁ ≤ m ∧ 1 ≤ r ∧ r ≤ 2 * a ∧ Fintype.card E = (p ^ s) ^ r ∧ (p ^ a) ^ (2 * m) = (p ^ s) ^ r ∧
        Cm ≠ ⊥ ∧ Cm ≤ D ∧ fm ∈ D ∧ gm ∈ D ∧
        Nat.card D ≤ (p ^ s) ^ (r * Nat.choose (a * m + 2 * a * (p - 1)) (2 * a * (p - 1))) ∧
        (Lm (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ) < (minD (nm (p ^ a) m) Cm : ℝ) / (nm (p ^ a) m : ℝ) ∧
        (minD (nm (p ^ a) m) Cm : ℝ) / (nm (p ^ a) m : ℝ) < 3 * (em (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ) ∧
        4 * (em (p ^ a) m : ℝ) / (3 * (nm (p ^ a) m : ℝ)) <
          (dE (nm (p ^ a) m) fm Cm : ℝ) / (nm (p ^ a) m : ℝ) ∧
        4 * (em (p ^ a) m : ℝ) / (3 * (nm (p ^ a) m : ℝ)) <
          (dE (nm (p ^ a) m) gm Cm : ℝ) / (nm (p ^ a) m : ℝ) ∧
        c * ((p ^ s : ℕ) : ℝ) ≤ (T.card : ℝ) ∧
        ∀ z ∈ T, (dE (nm (p ^ a) m) (fm + z • gm) Cm : ℝ) / (nm (p ^ a) m : ℝ) ≤
          (em (p ^ a) m : ℝ) / (nm (p ^ a) m : ℝ) := by
  classical
  obtain ⟨m₀, hm₀⟩ := lemma_3_4_shortenings p a hQ h49 h121
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp at hQ
    · exact h
  have hpp : p.Prime := Fact.out
  set M0 := max m₀ (max 4 m₁) with hM0
  have hM04 : 4 ≤ M0 := le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨1 / (4 * ((p ^ a : ℕ) : ℝ) ^ 4), by positivity, 2 * a * M0, ?_⟩
  intro s hs F _ _ _ hF
  have hs0 : 0 < s := lt_of_lt_of_le
    (Nat.mul_pos (Nat.mul_pos two_pos hapos) (by omega)) hs
  obtain ⟨d, hd⟩ : ∃ d, d = Nat.gcd s (2 * a) := ⟨_, rfl⟩
  have hd0 : 0 < d := hd ▸ Nat.gcd_pos_of_pos_left _ hs0
  obtain ⟨m, hm⟩ : d ∣ s := hd ▸ Nat.gcd_dvd_left _ _
  obtain ⟨r, hr⟩ : d ∣ 2 * a := hd ▸ Nat.gcd_dvd_right _ _
  have hdle : d ≤ 2 * a := Nat.le_of_dvd (by omega) ⟨r, hr⟩
  have hM0m : M0 ≤ m := by
    have h1 : d * M0 ≤ d * m := by
      calc d * M0 ≤ 2 * a * M0 := Nat.mul_le_mul_right _ hdle
        _ ≤ s := hs
        _ = d * m := hm
    exact Nat.le_of_mul_le_mul_left h1 hd0
  have hm4 : 4 ≤ m := le_trans hM04 hM0m
  have hm₀m : m₀ ≤ m := le_trans (le_trans (le_max_left _ _) (le_refl M0)) hM0m
  have hm₁m : m₁ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _) |>.trans (le_refl M0)) hM0m
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; omega
    · exact h
  have hr2 : r ≤ 2 * a := by nlinarith
  have hsr : s * r = 2 * a * m := by
    calc s * r = d * m * r := by rw [← hm]
      _ = (d * r) * m := by ring
      _ = 2 * a * m := by rw [← hr]
  have hm0' : 2 * a * m ≠ 0 := by positivity
  let E := GaloisField p (2 * a * m)
  letI : Fintype E := Fintype.ofFinite _
  have hEcard : Fintype.card E = p ^ (2 * a * m) := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p _ hm0'
  letI : Fintype (GaloisField p a) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField p a) = p ^ a := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p a hapos.ne'
  -- characteristic of F
  obtain ⟨p', hp'⟩ := CharP.exists F
  obtain ⟨n, hpr, hcard⟩ := FiniteField.card F p'
  have hdvd : p' ∣ p ^ s := by
    have : p' ∣ Fintype.card F := by
      rw [hcard]; exact dvd_pow_self p' (by exact n.pos.ne')
    rwa [hF] at this
  have hpp' : p' = p :=
    (Nat.prime_dvd_prime_iff_eq hpr hpp).mp (hpr.dvd_of_dvd_pow hdvd)
  have hcp : CharP F p := hpp' ▸ hp'
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  have hfrF : Module.finrank (ZMod p) F = s := by
    have := FiniteField.pow_finrank_eq_card p F
    rw [hF] at this
    exact Nat.pow_right_injective hpp.two_le this
  have hfrE : Module.finrank (ZMod p) E = 2 * a * m := by
    have := FiniteField.pow_finrank_eq_card p E
    rw [hEcard] at this
    exact Nat.pow_right_injective hpp.two_le this
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p) (K := F) (L := E)
    (by rw [hfrF, hfrE, ← hsr]; exact Dvd.intro _ rfl)
  letI : Algebra F E := φ.toRingHom.toAlgebra
  have hEq : Fintype.card E = (p ^ a) ^ (2 * m) := by
    rw [hEcard, ← pow_mul]; congr 1; ring
  have hEq2 : Fintype.card E = (p ^ s) ^ r := by
    rw [hEcard, ← pow_mul, hsr]
  have hF2 : 2 ≤ Fintype.card F := by
    rw [hF]
    calc 2 ≤ p := hpp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ s := Nat.pow_le_pow_right hpp.pos hs0
  obtain ⟨h1, h2, -⟩ := hm₀ m hm₀m (GaloisField p a) hK
  obtain ⟨Cm, D, fm, gm, T, hCb, hCD, hfD, hgD, hDc, hmn1, hmn2, hdf, hdg, hT, hz⟩ :=
    core p a m hm4 (GaloisField p a) hK (by omega) h1 h2 F E hEq hF2
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, m, r, Cm, D, fm, gm, T,
    hm₁m, hr1, hr2, hEq2, hEq ▸ hEq2, hCb, hCD, hfD, hgD, ?_, hmn1, hmn2, hdf, hdg, ?_, hz⟩
  · calc Nat.card D ≤ _ := hDc
      _ = _ := by rw [hEq2, ← pow_mul]
  · rw [hF] at hT; exact hT

end ProxGapTight.Dev.Main
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ProxGapTight.Dev.Enlarge

open Module

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {N : ℕ}

lemma card_ball (w : ℕ) :
    (Finset.univ.filter fun x : Fin N → F => hammingNorm x ≤ w).card ≤
      2 ^ N * Fintype.card F ^ w := by
  classical
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have hsub : (Finset.univ.filter fun x : Fin N → F => hammingNorm x ≤ w) ⊆
      (Finset.univ.filter fun s : Finset (Fin N) => s.card ≤ w).biUnion
        (fun s => Fintype.piFinset fun i => if i ∈ s then (Finset.univ : Finset F) else {0}) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]
    refine ⟨Finset.univ.filter (fun i => x i ≠ 0), ?_, ?_⟩
    · simpa [hammingNorm] using hx
    · intro i
      by_cases hi : x i = 0 <;> simp [hi]
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  have h1 : ∀ s ∈ (Finset.univ.filter fun s : Finset (Fin N) => s.card ≤ w),
      (Fintype.piFinset fun i => if i ∈ s then (Finset.univ : Finset F) else {0}).card
        ≤ Fintype.card F ^ w := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [Fintype.card_piFinset]
    have : ∀ i : Fin N, (if i ∈ s then (Finset.univ : Finset F) else {0}).card =
        if i ∈ s then Fintype.card F else 1 := by
      intro i; split_ifs <;> simp
    simp only [this]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    have : (Finset.univ.filter fun i => i ∈ s).card = s.card := by simp
    rw [this]
    exact Nat.pow_le_pow_right hq hs
  refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
  rw [smul_eq_mul]
  refine Nat.mul_le_mul ?_ le_rfl
  calc _ ≤ Fintype.card (Finset (Fin N)) := Finset.card_le_univ _
    _ = 2 ^ N := by simp

/-- Singleton bound. -/
lemma finrank_le_singleton (C : Submodule F (Fin N → F)) (hC : C ≠ ⊥) :
    finrank F C + minDist C ≤ N + 1 := by
  classical
  have hne : {w : ℕ | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = w}.Nonempty := by
    obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff C).1 hC
    exact ⟨_, c, hc, hc0, rfl⟩
  obtain ⟨c0, hc0C, hc00, hc0w⟩ := Nat.sInf_mem hne
  have hd1 : 1 ≤ minDist C := by
    unfold minDist; rw [← hc0w]; exact hammingNorm_pos_iff.2 hc00
  have hdN : minDist C ≤ N := by
    unfold minDist; rw [← hc0w]
    simpa using hammingNorm_le_card_fintype (x := c0)
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin N))) (n := N + 1 - minDist C) (by simp; omega)
  let π : (Fin N → F) →ₗ[F] (T → F) := LinearMap.funLeft F F (Subtype.val : T → Fin N)
  have hinj : Function.Injective (π.domRestrict C) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hc' : π c.1 = 0 := by simpa using hc
    by_contra hne0
    have hcne : c.1 ≠ 0 := fun h => hne0 (Subtype.ext h)
    have hle : minDist C ≤ hammingNorm c.1 := Nat.sInf_le ⟨c.1, c.2, hcne, rfl⟩
    have hsup : Finset.univ.filter (fun i => c.1 i ≠ 0) ⊆ Tᶜ := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_compl]
      intro hiT
      apply hi
      have := congrFun hc' ⟨i, hiT⟩
      simpa [π, LinearMap.funLeft] using this
    have := Finset.card_le_card hsup
    rw [Finset.card_compl, hT, Fintype.card_fin] at this
    have e : hammingNorm c.1 = (Finset.univ.filter (fun i => c.1 i ≠ 0)).card := rfl
    omega
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [finrank_fintype_fun_eq_card, Fintype.card_coe, hT] at this
  omega


lemma minDist_spec (C0 : Submodule F (Fin N → F)) (hC0 : C0 ≠ ⊥) :
    ∃ c ∈ C0, c ≠ 0 ∧ hammingNorm c = minDist C0 := by
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff C0).1 hC0
  exact Nat.sInf_mem (s := {w : ℕ | ∃ c ∈ C0, c ≠ 0 ∧ hammingNorm c = w}) ⟨_, c, hc, hc0, rfl⟩

lemma minDist_le (C0 : Submodule F (Fin N → F)) (c : Fin N → F) (hc : c ∈ C0) (h0 : c ≠ 0) :
    minDist C0 ≤ hammingNorm c := Nat.sInf_le ⟨c, hc, h0, rfl⟩

/-- Near-MDS enlargement (end of the proof of Theorem 3.1). -/
theorem enlarge (C0 : Submodule F (Fin N → F)) (hC0 : C0 ≠ ⊥) (f g : Fin N → F) (b0 : ℕ)
    (hb : b0 < minDist C0)
    (hf : ∀ u : Fin N → F, hammingNorm u ≤ b0 → f - u ∉ C0)
    (hg : ∀ u : Fin N → F, hammingNorm u ≤ b0 → g - u ∉ C0)
    (h : ℕ) (hh : 8 * 2 ^ N ≤ Fintype.card F ^ h) :
    ∃ C : Submodule F (Fin N → F), C0 ≤ C ∧ minDist C = minDist C0 ∧
      N + 1 ≤ finrank F C + minDist C0 + h ∧
      (∀ u : Fin N → F, hammingNorm u ≤ b0 → f - u ∉ C ∧ g - u ∉ C) := by
  classical
  set d0 := minDist C0 with hd0
  by_cases hd : finrank F C0 + d0 + h < N + 1
  swap
  · exact ⟨C0, le_rfl, rfl, by omega, fun u hu => ⟨hf u hu, hg u hu⟩⟩
  obtain ⟨c0, hc0C, hc00, hc0w⟩ := minDist_spec C0 hC0
  have hc0w : hammingNorm c0 = d0 := hc0w
  have hd1 : 1 ≤ d0 := by rw [← hc0w]; exact hammingNorm_pos_iff.2 hc00
  have hdN : d0 ≤ N := by
    rw [← hc0w]; simpa using hammingNorm_le_card_fintype (x := c0)
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  set K := N + 1 - d0 - h with hK
  have hKr : finrank F C0 + 1 ≤ K := by omega
  have hKN : K ≤ N := by omega
  have : Finite (Submodule F (Fin N → F)) :=
    Finite.of_injective (fun C : Submodule F (Fin N → F) => (C : Set (Fin N → F)))
      SetLike.coe_injective
  have : Fintype (Submodule F (Fin N → F)) := Fintype.ofFinite _
  have e : ∀ (P : Submodule F (Fin N → F) → Prop) [DecidablePred P],
      Set.ncard {C | P C} = (Finset.univ.filter P).card := by
    intro P _
    rw [← Set.ncard_coe_finset]
    congr 1
    ext C; simp
  -- the bad set
  let ball : ℕ → Finset (Fin N → F) := fun w => Finset.univ.filter fun x => hammingNorm x ≤ w
  let S : Finset (Fin N → F) := Finset.univ.filter fun x =>
    x ∉ C0 ∧ (hammingNorm x ≤ d0 - 1 ∨ (∃ u, hammingNorm u ≤ b0 ∧ x = f - u) ∨
      (∃ u, hammingNorm u ≤ b0 ∧ x = g - u))
  have hSsub : S ⊆ ball (d0 - 1) ∪ ((ball b0).image (fun u => f - u) ∪
      (ball b0).image (fun u => g - u)) := by
    intro x hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨-, hx | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩⟩ := hx
    · simp [ball, hx]
    · simp only [ball, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
    · simp only [ball, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inr (Or.inr ⟨u, hu, rfl⟩)
  set q := Fintype.card F with hqdef
  have hpos : 0 < 2 ^ N * q ^ (d0 - 1) := by positivity
  have hSc : S.card ≤ 3 * (2 ^ N * q ^ (d0 - 1)) := by
    have b1 := card_ball (F := F) (N := N) (d0 - 1)
    have b2 := card_ball (F := F) (N := N) b0
    have hqq : q ^ b0 ≤ q ^ (d0 - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have c1 := (Finset.card_le_card hSsub).trans (Finset.card_union_le _ _)
    have c2 := Finset.card_union_le ((ball b0).image (fun u => f - u))
      ((ball b0).image (fun u => g - u))
    have c3 := Finset.card_image_le (s := ball b0) (f := fun u => f - u)
    have c4 := Finset.card_image_le (s := ball b0) (f := fun u => g - u)
    have : 2 ^ N * q ^ b0 ≤ 2 ^ N * q ^ (d0 - 1) := Nat.mul_le_mul le_rfl hqq
    rw [← hqdef] at b1 b2
    simp only [ball] at *
    omega
  have hSq : S.card * 2 < q ^ (d0 - 1 + h) := by
    rw [pow_add]
    have : 8 * (2 ^ N * q ^ (d0 - 1)) ≤ q ^ h * q ^ (d0 - 1) := by
      calc _ = (8 * 2 ^ N) * q ^ (d0 - 1) := by ring
        _ ≤ _ := Nat.mul_le_mul hh le_rfl
    nlinarith
  -- double counting
  set T := (Finset.univ.filter fun C : Submodule F (Fin N → F) =>
    finrank F C = K ∧ C0 ≤ C).card with hT
  have hx : ∀ x : Fin N → F, x ∉ C0 → ((Finset.univ.filter fun C : Submodule F (Fin N → F) =>
      finrank F C = K ∧ C0 ≤ C ∧ x ∈ C).card : ℝ) ≤
        2 * (q : ℝ) ^ ((K : ℤ) - (N : ℤ)) * T ∧ 0 < (T : ℝ) := by
    intro x hxS
    obtain ⟨hr, hle2⟩ := ProxGapTight.supercode_prob F N K C0 (by omega) hKN x hxS
    rw [e, e, ← hT] at hr
    have hqR : (1 : ℝ) < q := by exact_mod_cast hq
    have h1 : (1 : ℝ) < (q : ℝ) ^ (K - finrank F C0) :=
      one_lt_pow₀ hqR (by omega)
    have h2 : (1 : ℝ) < (q : ℝ) ^ (N - finrank F C0) :=
      one_lt_pow₀ hqR (by omega)
    have hTpos : (0 : ℝ) < T := by
      by_contra hneg
      have h0 : (T : ℝ) = 0 := le_antisymm (not_lt.1 hneg) (by positivity)
      rw [h0, div_zero] at hr
      have : 0 < ((q : ℝ) ^ (K - finrank F C0) - 1) / ((q : ℝ) ^ (N - finrank F C0) - 1) :=
        div_pos (by linarith) (by linarith)
      linarith
    refine ⟨?_, hTpos⟩
    have := (div_le_iff₀ hTpos).1 (hr ▸ hle2)
    linarith
  obtain ⟨x0, hx0⟩ : ∃ x0 : Fin N → F, x0 ∉ C0 := by
    by_contra hcon
    push Not at hcon
    have : C0 = ⊤ := Submodule.eq_top_iff'.2 hcon
    have hfr : finrank F C0 = N := by rw [this]; simp
    omega
  have hTpos : (0 : ℝ) < T := (hx x0 hx0).2
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hexp : (q : ℝ) ^ ((K : ℤ) - (N : ℤ)) = ((q : ℝ) ^ (d0 - 1 + h))⁻¹ := by
    have : (K : ℤ) - (N : ℤ) = -((d0 - 1 + h : ℕ) : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast]
  have hSq' : (S.card : ℝ) * 2 < (q : ℝ) ^ (d0 - 1 + h) := by exact_mod_cast hSq
  have hqp : (0 : ℝ) < (q : ℝ) ^ (d0 - 1 + h) := by positivity
  have hfin : (S.card : ℝ) * (2 * (q : ℝ) ^ ((K : ℤ) - (N : ℤ))) < 1 := by
    rw [hexp]
    rw [← mul_assoc, ← div_eq_mul_inv, div_lt_one hqp]
    linarith
  -- find a good supercode
  have hgood : ∃ C : Submodule F (Fin N → F), finrank F C = K ∧ C0 ≤ C ∧ ∀ x ∈ S, x ∉ C := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ.filter fun C : Submodule F (Fin N → F) => finrank F C = K ∧ C0 ≤ C) ⊆
        S.biUnion (fun x => Finset.univ.filter fun C : Submodule F (Fin N → F) =>
          finrank F C = K ∧ C0 ≤ C ∧ x ∈ C) := by
      intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      obtain ⟨x, hxS, hxC⟩ := hcon C hC.1 hC.2
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hxS, hC.1, hC.2, hxC⟩
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : (T : ℝ) ≤ ∑ x ∈ S, ((Finset.univ.filter fun C : Submodule F (Fin N → F) =>
        finrank F C = K ∧ C0 ≤ C ∧ x ∈ C).card : ℝ) := by exact_mod_cast h1
    have h3 : ∑ x ∈ S, ((Finset.univ.filter fun C : Submodule F (Fin N → F) =>
        finrank F C = K ∧ C0 ≤ C ∧ x ∈ C).card : ℝ) ≤
        ∑ _x ∈ S, 2 * (q : ℝ) ^ ((K : ℤ) - (N : ℤ)) * T := by
      refine Finset.sum_le_sum fun x hxS => (hx x ?_).1
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hxS
      exact hxS.1
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    have : (T : ℝ) * 1 ≤ (T : ℝ) * ((S.card : ℝ) * (2 * (q : ℝ) ^ ((K : ℤ) - (N : ℤ)))) := by
      nlinarith
    nlinarith
  obtain ⟨C, hCK, hC0C, hCS⟩ := hgood
  have hCne : ∀ u : Fin N → F, hammingNorm u ≤ b0 → f - u ∉ C ∧ g - u ∉ C := by
    intro u hu
    refine ⟨fun hmem => hCS _ ?_ hmem, fun hmem => hCS _ ?_ hmem⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hf u hu, Or.inr (Or.inl ⟨u, hu, rfl⟩)⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hg u hu, Or.inr (Or.inr ⟨u, hu, rfl⟩)⟩
  refine ⟨C, hC0C, ?_, by omega, hCne⟩
  apply le_antisymm
  · have : minDist C ≤ hammingNorm c0 := minDist_le C c0 (hC0C hc0C) hc00
    omega
  · obtain ⟨c, hcC, hc0', hcw⟩ := minDist_spec C (by
      intro hbot; rw [hbot] at hC0C
      exact hc00 (by simpa using hC0C hc0C))
    by_contra hlt
    push Not at hlt
    apply hCS c _ hcC
    have hnot : c ∉ C0 := fun hm => by
      have := minDist_le C0 c hm hc0'
      omega
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hnot, Or.inl (by omega)⟩

end ProxGapTight.Dev.Enlarge
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ProxGapTight.Dev.Main1
open ProxGapTight ProxGapTight.Dev.Main

section Phi

lemma Phi_mono {t : ℕ} {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    Phi t u ≤ Phi t v := by
  unfold Phi
  have : (1 - v) ^ t ≤ (1 - u) ^ t := pow_le_pow_left₀ (by linarith) (by linarith) t
  linarith

lemma Phi_mem {t : ℕ} {u : ℝ} (hu : 0 ≤ u) (hv : u ≤ 1) : 0 ≤ Phi t u ∧ Phi t u ≤ 1 := by
  unfold Phi
  have h0 : 0 ≤ (1 - u) ^ t := pow_nonneg (by linarith) t
  have h1 : (1 - u) ^ t ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  constructor <;> linarith

end Phi

section Amp

variable {F E : Type} [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E]
  [Algebra F E]

/-- The amplification map as an `F`-linear map. -/
def ampLin {n t N : ℕ} (ω : Fin N → AmpSample F E n t) : (Fin n → E) →ₗ[F] (Fin N → F) where
  toFun := amp ω
  map_add' v w := by
    funext j
    show (ω j).2 (fun k => v ((ω j).1 k) + w ((ω j).1 k)) = _
    have : (fun k => v ((ω j).1 k) + w ((ω j).1 k)) =
        (fun k => v ((ω j).1 k)) + (fun k => w ((ω j).1 k)) := rfl
    rw [this, map_add]; rfl
  map_smul' c v := by
    funext j
    show (ω j).2 (fun k => c • v ((ω j).1 k)) = _
    have : (fun k => c • v ((ω j).1 k)) = c • (fun k => v ((ω j).1 k)) := rfl
    rw [this, map_smul]; rfl

lemma ampLin_apply {n t N : ℕ} (ω : Fin N → AmpSample F E n t) (v : Fin n → E) :
    ampLin ω v = amp ω v := rfl

lemma wt_ratio_mem {ι : Type} [Fintype ι] {K : Type} [Zero K] [DecidableEq K] (v : ι → K)
    (hn : 0 < Fintype.card ι) :
    0 ≤ (hammingNorm v : ℝ) / (Fintype.card ι : ℝ) ∧
      (hammingNorm v : ℝ) / (Fintype.card ι : ℝ) ≤ 1 := by
  have hpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  constructor
  · positivity
  · rw [div_le_one hpos]; exact_mod_cast hammingNorm_le_card_fintype

lemma est2 {n t N : ℕ} (hn : 0 < n) (ξ : ℝ) (hq : 1 / (Fintype.card F : ℝ) < ξ)
    (ω : Fin N → AmpSample F E n t) (v : Fin n → E)
    (h : |(hammingNorm (amp ω v) : ℝ) / (N : ℝ) -
          (1 - 1 / (Fintype.card F : ℝ)) * Phi t ((hammingNorm v : ℝ) / (n : ℝ))| ≤ ξ) :
    |(hammingNorm (amp ω v) : ℝ) / (N : ℝ) - Phi t ((hammingNorm v : ℝ) / (n : ℝ))| < 2 * ξ := by
  have hm := wt_ratio_mem v (ι := Fin n) (by simpa using hn)
  simp only [Fintype.card_fin] at hm
  obtain ⟨hP0, hP1⟩ := Phi_mem (t := t) hm.1 hm.2
  set P := Phi t ((hammingNorm v : ℝ) / (n : ℝ))
  set a : ℝ := 1 / (Fintype.card F : ℝ) with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have haP : a * P ≤ a := mul_le_of_le_one_right ha0 hP1
  have haP0 : 0 ≤ a * P := mul_nonneg ha0 hP0
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]

variable {n t N : ℕ}

/-- The good-map hypothesis. -/
def Good (ω : Fin N → AmpSample F E n t) (ξ : ℝ) (D : Submodule F (Fin n → E)) : Prop :=
  ∀ v ∈ D, |(hammingNorm (amp ω v) : ℝ) / (N : ℝ) -
          (1 - 1 / (Fintype.card F : ℝ)) * Phi t ((hammingNorm v : ℝ) / (n : ℝ))| ≤ ξ

lemma dE_le (Cm : Submodule F (Fin n → E)) (x c : Fin n → E) (hc : c ∈ Cm) :
    dE n x Cm ≤ hammingNorm (x - c) := Nat.sInf_le ⟨c, hc, rfl⟩

lemma dE_spec (Cm : Submodule F (Fin n → E)) (x : Fin n → E) :
    ∃ c ∈ Cm, hammingNorm (x - c) = dE n x Cm :=
  Nat.sInf_mem (s := {w : ℕ | ∃ c ∈ Cm, hammingNorm (x - c) = w}) ⟨_, 0, Cm.zero_mem, rfl⟩

lemma minD_le (Cm : Submodule F (Fin n → E)) (c : Fin n → E) (hc : c ∈ Cm) (h0 : c ≠ 0) :
    minD n Cm ≤ hammingNorm c := Nat.sInf_le ⟨c, hc, h0, rfl⟩

lemma minD_spec (Cm : Submodule F (Fin n → E)) (hC : Cm ≠ ⊥) :
    ∃ c ∈ Cm, c ≠ 0 ∧ hammingNorm c = minD n Cm := by
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff Cm).1 hC
  exact Nat.sInf_mem (s := {w : ℕ | ∃ c ∈ Cm, c ≠ 0 ∧ hammingNorm c = w}) ⟨_, c, hc, hc0, rfl⟩

lemma hd_eq (ω : Fin N → AmpSample F E n t) (x c : Fin n → E) :
    hammingDist (amp ω x) (ampLin ω c) = hammingNorm (amp ω (x - c)) := by
  have e : amp ω (x - c) = amp ω x - ampLin ω c := by
    rw [← ampLin_apply, map_sub]; rfl
  rw [e]
  simp only [hammingDist, hammingNorm, Pi.sub_apply, sub_ne_zero]

lemma distToCode_gt (ω : Fin N → AmpSample F E n t) (hN : 0 < N) (Cm : Submodule F (Fin n → E))
    (x : Fin n → E) (B : ℝ)
    (hB : ∀ c ∈ Cm, B < (hammingNorm (amp ω (x - c)) : ℝ) / (N : ℝ)) :
    B < distToCode (amp ω x) (Cm.map (ampLin ω)) := by
  classical
  unfold distToCode
  have hne : {w : ℕ | ∃ c ∈ Cm.map (ampLin ω), hammingDist (amp ω x) c = w}.Nonempty :=
    ⟨_, 0, Submodule.zero_mem _, rfl⟩
  obtain ⟨c', hc', hw⟩ := Nat.sInf_mem hne
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hc'
  rw [← hw, Fintype.card_fin, hd_eq]
  exact hB c hc

lemma distToCode_le (ω : Fin N → AmpSample F E n t) (hN : 0 < N) (Cm : Submodule F (Fin n → E))
    (x c : Fin n → E) (hc : c ∈ Cm) :
    distToCode (amp ω x) (Cm.map (ampLin ω)) ≤ (hammingNorm (amp ω (x - c)) : ℝ) / (N : ℝ) := by
  classical
  unfold distToCode
  rw [Fintype.card_fin]
  have hle : sInf {w : ℕ | ∃ c' ∈ Cm.map (ampLin ω), hammingDist (amp ω x) c' = w} ≤
      hammingNorm (amp ω (x - c)) := by
    refine Nat.sInf_le ⟨ampLin ω c, Submodule.mem_map_of_mem hc, ?_⟩
    exact hd_eq ω x c
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hNr.le

end Amp

section Analysis

variable {F E : Type} [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E]
  [Algebra F E] {n t N : ℕ}

lemma gw (hn : 0 < n) (ω : Fin N → AmpSample F E n t) (ξ : ℝ)
    (hq : 1 / (Fintype.card F : ℝ) < ξ) (D : Submodule F (Fin n → E)) (hg : Good ω ξ D)
    (v : Fin n → E) (hv : v ∈ D) :
    |(hammingNorm (amp ω v) : ℝ) / (N : ℝ) - Phi t ((hammingNorm v : ℝ) / (n : ℝ))| < 2 * ξ :=
  est2 hn ξ hq ω v (hg v hv)

lemma lower_dist (hn : 0 < n) (ω : Fin N → AmpSample F E n t) (ξ : ℝ)
    (hq : 1 / (Fintype.card F : ℝ) < ξ) (D Cm : Submodule F (Fin n → E)) (hCD : Cm ≤ D)
    (hg : Good ω ξ D) (x : Fin n → E) (hx : x ∈ D) (c : Fin n → E) (hc : c ∈ Cm) :
    Phi t ((dE n x Cm : ℝ) / (n : ℝ)) - 2 * ξ <
      (hammingNorm (amp ω (x - c)) : ℝ) / (N : ℝ) := by
  have h1 := gw hn ω ξ hq D hg (x - c) (D.sub_mem hx (hCD hc))
  rw [abs_lt] at h1
  have hm := wt_ratio_mem (x - c) (ι := Fin n) (by simpa using hn)
  simp only [Fintype.card_fin] at hm
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (dE n x Cm : ℝ) / n ≤ (hammingNorm (x - c) : ℝ) / n :=
    div_le_div_of_nonneg_right (by exact_mod_cast dE_le Cm x c hc) hnr.le
  have := Phi_mono (t := t) (by positivity) hle hm.2
  linarith [h1.1]

lemma amp_nonzero_of_dist {x : Fin n → E} {ω : Fin N → AmpSample F E n t} {B : ℝ} (hB : 0 ≤ B)
    (hN : 0 < N) (h : B < (hammingNorm (amp ω x) : ℝ) / (N : ℝ)) : amp ω x ≠ 0 := by
  intro h0
  rw [h0] at h
  simp at h
  linarith

theorem analysis (hn : 0 < n) (hN : 0 < N) (ω : Fin N → AmpSample F E n t)
    (ξ δ Γ ρ η0 : ℝ) (L e : ℕ)
    (he : e ≤ n) (hξ : 0 < ξ) (hξη : ξ ≤ η0 / 8) (hηδ : 4 * η0 ≤ δ) (hη0 : 0 < η0)
    (hq : 1 / (Fintype.card F : ℝ) < ξ)
    (Cm D : Submodule F (Fin n → E)) (fm gm : Fin n → E) (T : Finset F)
    (hCD : Cm ≤ D) (hf : fm ∈ D) (hg : gm ∈ D) (hCbot : Cm ≠ ⊥)
    (hgood : Good ω ξ D)
    (H1 : Phi t ((e : ℝ) / n) + 3 * ξ < ρ)
    (H2 : Γ < Phi t (4 * (e : ℝ) / (3 * n)) - 3 * ξ)
    (H3 : ∀ u ∈ Set.Icc ((L : ℝ) / n) (3 * (e : ℝ) / n), |Phi t u - δ| < η0 / 2)
    (hd1 : (L : ℝ) / n < (minD n Cm : ℝ) / n) (hd2 : (minD n Cm : ℝ) / n < 3 * (e : ℝ) / n)
    (hdf : 4 * (e : ℝ) / (3 * n) < (dE n fm Cm : ℝ) / n)
    (hdg : 4 * (e : ℝ) / (3 * n) < (dE n gm Cm : ℝ) / n)
    (hT : ∀ z ∈ T, (dE n (fm + z • gm) Cm : ℝ) / n ≤ (e : ℝ) / n) :
    Cm.map (ampLin ω) ≠ ⊥ ∧ |relDist (Cm.map (ampLin ω)) - δ| < η0 ∧
      Γ < distToCode (amp ω fm) (Cm.map (ampLin ω)) ∧
      Γ < distToCode (amp ω gm) (Cm.map (ampLin ω)) ∧
      ∀ z ∈ T, distToCode (amp ω fm + z • amp ω gm) (Cm.map (ampLin ω)) ≤ ρ := by
  classical
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- distances of f, g
  have hdist : ∀ x ∈ D, 4 * (e : ℝ) / (3 * n) < (dE n x Cm : ℝ) / n →
      Γ < distToCode (amp ω x) (Cm.map (ampLin ω)) := by
    intro x hx hdx
    refine distToCode_gt ω hN Cm x Γ ?_
    intro c hc
    have h1 := lower_dist hn ω ξ hq D Cm hCD hgood x hx c hc
    have h2 := Phi_mono (t := t) (u := 4 * (e : ℝ) / (3 * n)) (by positivity) hdx.le
      (by
        have : (dE n x Cm : ℝ) ≤ n := by
          obtain ⟨c0, hc0, hw⟩ := dE_spec Cm x
          rw [← hw]; exact_mod_cast (by simpa using hammingNorm_le_card_fintype (x := x - c0))
        rw [div_le_one hnr]; exact this)
    linarith
  -- minimum distance
  obtain ⟨c1, hc1, hc10, hc1w⟩ := minD_spec Cm hCbot
  have hdm_mem : (minD n Cm : ℝ) / n ∈ Set.Icc ((L : ℝ) / n) (3 * (e : ℝ) / n) := ⟨hd1.le, hd2.le⟩
  have hPd := H3 _ hdm_mem
  rw [abs_lt] at hPd
  have hc1D : c1 ∈ D := hCD hc1
  have hw1 := gw hn ω ξ hq D hgood c1 hc1D
  rw [abs_lt, hc1w] at hw1
  have hξ2 : 2 * ξ ≤ η0 / 4 := by linarith
  have hnz : amp ω c1 ≠ 0 := by
    refine amp_nonzero_of_dist (B := 0) le_rfl hN ?_
    linarith [hw1.1, hPd.1]
  have hmem1 : amp ω c1 ∈ Cm.map (ampLin ω) := Submodule.mem_map.2 ⟨c1, hc1, rfl⟩
  have hC0bot : Cm.map (ampLin ω) ≠ ⊥ := by
    intro h; rw [h] at hmem1; exact hnz ((Submodule.mem_bot F).1 hmem1)
  refine ⟨hC0bot, ?_, hdist fm hf hdf, hdist gm hg hdg, ?_⟩
  · have hrel : relDist (Cm.map (ampLin ω)) = (minDist (Cm.map (ampLin ω)) : ℝ) / (N : ℝ) := by
      unfold relDist; rw [Fintype.card_fin]
    rw [hrel, abs_lt]
    constructor
    · obtain ⟨c', hc', hc'0, hw⟩ := Enlarge.minDist_spec (Cm.map (ampLin ω)) hC0bot
      obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hc'
      have hc0 : c ≠ 0 := by rintro rfl; exact hc'0 (map_zero _)
      have hcD : c ∈ D := hCD hc
      have hw2 := gw hn ω ξ hq D hgood c hcD
      rw [abs_lt] at hw2
      have hmono : Phi t ((minD n Cm : ℝ) / n) ≤ Phi t ((hammingNorm c : ℝ) / n) := by
        have hm := wt_ratio_mem c (ι := Fin n) (by simpa using hn)
        simp only [Fintype.card_fin] at hm
        exact Phi_mono (by positivity)
          (div_le_div_of_nonneg_right (by exact_mod_cast minD_le Cm c hc hc0) hnr.le) hm.2
      rw [ampLin_apply] at hw
      have : (minDist (Cm.map (ampLin ω)) : ℝ) = hammingNorm (amp ω c) := by
        exact_mod_cast hw.symm
      rw [this]
      linarith [hw2.1, hPd.1]
    · have hle : minDist (Cm.map (ampLin ω)) ≤ hammingNorm (amp ω c1) :=
        Enlarge.minDist_le _ _ hmem1 hnz
      have : (minDist (Cm.map (ampLin ω)) : ℝ) / N ≤ (hammingNorm (amp ω c1) : ℝ) / N :=
        div_le_div_of_nonneg_right (by exact_mod_cast hle) hNr.le
      linarith [hw1.2, hPd.2]
  · intro z hz
    obtain ⟨c, hc, hw⟩ := dE_spec Cm (fm + z • gm)
    have e1 : amp ω fm + z • amp ω gm = amp ω (fm + z • gm) := by
      have h := (ampLin ω).map_add fm (z • gm)
      rw [(ampLin ω).map_smul] at h
      exact h.symm
    rw [e1]
    refine (distToCode_le ω hN Cm _ c hc).trans ?_
    have hxD : fm + z • gm ∈ D := D.add_mem hf (D.smul_mem z hg)
    have h2 := gw hn ω ξ hq D hgood _ (D.sub_mem hxD (hCD hc))
    rw [abs_lt] at h2
    rw [hw] at h2
    have hdle := hT z hz
    have hm : (dE n (fm + z • gm) Cm : ℝ) / n ≤ 1 := by
      exact hdle.trans ((div_le_one hnr).2 (by exact_mod_cast he))
    have := Phi_mono (t := t) (by positivity) hdle ((div_le_one hnr).2 (by exact_mod_cast he))
    linarith [h2.2]

end Analysis

end ProxGapTight.Dev.Main1
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProxGapTight.Dev.Main2
open ProxGapTight ProxGapTight.Dev.Main1

section Exists

variable {F E : Type} [Field F] [Fintype F] [DecidableEq F] [Field E] [Fintype E] [DecidableEq E]
  [Algebra F E]

theorem exists_good (n t N : ℕ) (hn : 0 < n) (ht : 1 ≤ t) (hN : 1 ≤ N) (ξ : ℝ) (hξ : 0 < ξ)
    (D : Submodule F (Fin n → E))
    (hD : (Nat.card D : ℝ) * (2 * Real.exp (-2 * ξ ^ 2 * (N : ℝ))) < 1) :
    ∃ ω : Fin N → AmpSample F E n t, Good ω ξ D := by
  classical
  by_contra hcon
  rw [not_exists] at hcon
  have hcon' : ∀ ω : Fin N → AmpSample F E n t, ∃ v ∈ D, ξ < |(hammingNorm (amp ω v) : ℝ) / (N : ℝ) -
          (1 - 1 / (Fintype.card F : ℝ)) * Phi t ((hammingNorm v : ℝ) / (n : ℝ))| := by
    intro ω
    by_contra h
    push_neg at h
    exact hcon ω h
  haveI : Nonempty (Fin N → AmpSample F E n t) :=
    ⟨fun _ => ((fun _ => ⟨0, hn⟩, 0) : AmpSample F E n t)⟩
  haveI : Fintype (Fin N → AmpSample F E n t) := Fintype.ofFinite _
  haveI : Fintype D := Fintype.ofFinite _
  set B : ℝ := 2 * Real.exp (-2 * ξ ^ 2 * (N : ℝ)) with hB
  let bad : D → Finset (Fin N → AmpSample F E n t) := fun v =>
    Finset.univ.filter (fun ω => ξ < |(hammingNorm (amp ω v.1) : ℝ) / (N : ℝ) -
          (1 - 1 / (Fintype.card F : ℝ)) * Phi t ((hammingNorm v.1 : ℝ) / (n : ℝ))|)
  have hcover : (Finset.univ : Finset (Fin N → AmpSample F E n t)) ⊆
      Finset.univ.biUnion bad := by
    intro ω _
    obtain ⟨v, hv, hlt⟩ := hcon' ω
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨⟨v, hv⟩, by simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt⟩
  have hΩ : (0 : ℝ) < Fintype.card (Fin N → AmpSample F E n t) := by exact_mod_cast Fintype.card_pos
  have hch : ∀ v : D, ((bad v).card : ℝ) ≤ B * Fintype.card (Fin N → AmpSample F E n t) := by
    intro v
    have h := amp_chernoff F E n t N hn ht hN ξ hξ v.1
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos)] at h
    exact h
  have hsum : (Fintype.card (Fin N → AmpSample F E n t) : ℝ) ≤
      (Fintype.card D : ℝ) * (B * Fintype.card (Fin N → AmpSample F E n t)) := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_biUnion_le (s := (Finset.univ : Finset D)) (t := bad)
    have h3 : (Finset.univ : Finset (Fin N → AmpSample F E n t)).card ≤
        ∑ v : D, (bad v).card := by simpa using h1.trans h2
    have h4 : ((∑ v : D, (bad v).card : ℕ) : ℝ) ≤
        ∑ v : D, B * Fintype.card (Fin N → AmpSample F E n t) := by
      push_cast
      exact Finset.sum_le_sum (fun v _ => hch v)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h4
    have : (Fintype.card (Fin N → AmpSample F E n t) : ℝ) ≤ ((∑ v : D, (bad v).card : ℕ) : ℝ) := by
      exact_mod_cast (by simpa using h3)
    linarith
  rw [Nat.card_eq_fintype_card] at hD
  nlinarith

end Exists

section Arith

lemma choose_bound (a e s m : ℕ) (hs : 1 ≤ s) (hm : m ≤ s) :
    Nat.choose (a * m + e) e ≤ (a + e) ^ e * s ^ e := by
  calc Nat.choose (a * m + e) e ≤ (a * m + e) ^ e := Nat.choose_le_pow _ _
    _ ≤ ((a + e) * s) ^ e := by
        apply Nat.pow_le_pow_left
        nlinarith
    _ = _ := mul_pow _ _ _

theorem arith (p a : ℕ) (hp : 2 ≤ p) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ A : ℝ, 0 < A ∧ ∀ s m r : ℕ, 1 ≤ s → m ≤ s → r ≤ 2 * a → ∀ N : ℕ,
      A * (s : ℝ) ^ (2 * a * (p - 1) + 1) ≤ (N : ℝ) →
      (((p ^ s) ^ (r * Nat.choose (a * m + 2 * a * (p - 1)) (2 * a * (p - 1))) : ℕ) : ℝ) *
        (2 * Real.exp (-2 * ξ ^ 2 * (N : ℝ))) < 1 := by
  set e := 2 * a * (p - 1) with he
  set Bn : ℕ := (a + e) ^ e with hBn
  set M : ℝ := 2 * a * Bn * p with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨(M + 1) / (2 * ξ ^ 2), by positivity, ?_⟩
  intro s m r hs hm hr N hN
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hk := choose_bound a e s m hs hm
  -- exponent bound
  have hexp : s * (r * Nat.choose (a * m + e) e) ≤ 2 * a * Bn * s ^ (e + 1) := by
    calc s * (r * Nat.choose (a * m + e) e) ≤ s * ((2 * a) * (Bn * s ^ e)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul hr hk
      _ = 2 * a * Bn * s ^ (e + 1) := by ring
  have hpe : (p : ℝ) ≤ Real.exp p := by linarith [Real.add_one_le_exp (p : ℝ)]
  have h1 : (((p ^ s) ^ (r * Nat.choose (a * m + e) e) : ℕ) : ℝ) ≤
      Real.exp (M * (s : ℝ) ^ (e + 1)) := by
    have : (((p ^ s) ^ (r * Nat.choose (a * m + e) e) : ℕ) : ℝ) = (p : ℝ) ^ (s * (r * Nat.choose (a * m + e) e)) := by
      push_cast; rw [← pow_mul]
    rw [this]
    calc (p : ℝ) ^ (s * (r * Nat.choose (a * m + e) e))
        ≤ (Real.exp p) ^ (s * (r * Nat.choose (a * m + e) e)) :=
          pow_le_pow_left₀ (by positivity) hpe _
      _ = Real.exp (p * (s * (r * Nat.choose (a * m + e) e) : ℕ)) := by
          rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (M * (s : ℝ) ^ (e + 1)) := by
          apply Real.exp_le_exp.2
          have : ((s * (r * Nat.choose (a * m + e) e) : ℕ) : ℝ) ≤
              ((2 * a * Bn * s ^ (e + 1) : ℕ) : ℝ) := by exact_mod_cast hexp
          push_cast at this
          rw [hM]
          push_cast
          nlinarith [mul_le_mul_of_nonneg_left this (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have h2 : 2 * ξ ^ 2 * (N : ℝ) ≥ (M + 1) * (s : ℝ) ^ (e + 1) := by
    have : (M + 1) / (2 * ξ ^ 2) * (s : ℝ) ^ (e + 1) ≤ N := hN
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
    linarith
  have h3 : (1 : ℝ) ≤ (s : ℝ) ^ (e + 1) := one_le_pow₀ hsr
  have h4 : Real.exp (M * (s : ℝ) ^ (e + 1)) * (2 * Real.exp (-2 * ξ ^ 2 * (N : ℝ))) < 1 := by
    rw [mul_left_comm, ← Real.exp_add]
    have hx : M * (s : ℝ) ^ (e + 1) + -2 * ξ ^ 2 * (N : ℝ) ≤ -1 := by nlinarith
    have hex : Real.exp (M * (s : ℝ) ^ (e + 1) + -2 * ξ ^ 2 * (N : ℝ)) ≤ Real.exp (-1) :=
      Real.exp_le_exp.2 hx
    have h5 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    have h6 := Real.exp_one_gt_d9
    nlinarith [Real.exp_pos (-1 : ℝ), Real.exp_pos (M * (s : ℝ) ^ (e + 1) + -2 * ξ ^ 2 * (N : ℝ))]
  calc _ ≤ Real.exp (M * (s : ℝ) ^ (e + 1)) * (2 * Real.exp (-2 * ξ ^ 2 * (N : ℝ))) := by
        apply mul_le_mul_of_nonneg_right h1 (by positivity)
    _ < 1 := h4

end Arith

end ProxGapTight.Dev.Main2
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProxGapTight.Dev.Main3
open ProxGapTight Module

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {N : ℕ}

lemma hnorm_eq (x c : Fin N → F) : hammingNorm (x - c) = hammingDist x c := by
  simp only [hammingDist, hammingNorm, Pi.sub_apply, sub_ne_zero]

lemma distToCode_le_of_mem (C : Submodule F (Fin N → F)) (x c : Fin N → F) (hc : c ∈ C) :
    distToCode x C ≤ (hammingDist x c : ℝ) / (N : ℝ) := by
  classical
  unfold distToCode
  rw [Fintype.card_fin]
  have hle : sInf {w : ℕ | ∃ c' ∈ C, hammingDist x c' = w} ≤ hammingDist x c :=
    Nat.sInf_le ⟨c, hc, rfl⟩
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (Nat.cast_nonneg _)

lemma distToCode_mono (C0 C : Submodule F (Fin N → F)) (h : C0 ≤ C) (x : Fin N → F) :
    distToCode x C ≤ distToCode x C0 := by
  classical
  have hne : {w : ℕ | ∃ c ∈ C0, hammingDist x c = w}.Nonempty := ⟨_, 0, C0.zero_mem, rfl⟩
  obtain ⟨c, hc, hw⟩ := Nat.sInf_mem hne
  calc distToCode x C ≤ (hammingDist x c : ℝ) / (N : ℝ) := distToCode_le_of_mem C x c (h hc)
    _ = distToCode x C0 := by
        unfold distToCode
        rw [Fintype.card_fin, hw]

/-- distance to code exceeds Γ if no word within b0 of x lies in C. -/
lemma distToCode_gt_of (C : Submodule F (Fin N → F)) (hN : 0 < N) (x : Fin N → F) (Γ : ℝ)
    (b0 : ℕ) (hb0 : b0 = ⌊Γ * N⌋₊) (hΓ : 0 ≤ Γ) (hx : ∀ u : Fin N → F, hammingNorm u ≤ b0 → x - u ∉ C) :
    Γ < distToCode x C := by
  classical
  by_contra hcon
  rw [not_lt] at hcon
  have hne : {w : ℕ | ∃ c ∈ C, hammingDist x c = w}.Nonempty := ⟨_, 0, C.zero_mem, rfl⟩
  obtain ⟨c, hc, hw⟩ := Nat.sInf_mem hne
  unfold distToCode at hcon
  rw [Fintype.card_fin, ← hw] at hcon
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ hNr] at hcon
  have hle : hammingDist x c ≤ b0 := by
    rw [hb0]; exact Nat.le_floor hcon
  apply hx (x - c) (by rw [hnorm_eq]; exact hle)
  simpa using hc

/-- Minimal `h` with `8 * 2^N ≤ q^h` satisfies `s * h ≤ N + 2 + s` when `2^s ≤ q`. -/
lemma exists_h (q s N : ℕ) (hq : 2 ^ s ≤ q) (hs : 1 ≤ s) :
    ∃ h : ℕ, 1 ≤ h ∧ 8 * 2 ^ N ≤ q ^ h ∧ s * h ≤ N + 2 + s := by
  classical
  have hq2 : 2 ≤ q := le_trans (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs) hq
  have hex : ∃ h : ℕ, 8 * 2 ^ N ≤ q ^ h := ⟨8 * 2 ^ N, by
    have := Nat.lt_pow_self (n := 8 * 2 ^ N) (by omega : 1 < q)
    exact this.le⟩
  set h := Nat.find hex with hh
  have hspec : 8 * 2 ^ N ≤ q ^ h := Nat.find_spec hex
  have h1 : 1 ≤ h := by
    by_contra h0
    have : h = 0 := by omega
    rw [this] at hspec
    have : 1 ≤ 2 ^ N := Nat.one_le_two_pow
    simp at hspec; omega
  refine ⟨h, h1, hspec, ?_⟩
  have hmin : ¬ 8 * 2 ^ N ≤ q ^ (h - 1) := Nat.find_min hex (by omega)
  push_neg at hmin
  have : 2 ^ (s * (h - 1)) < 2 ^ (N + 3) := by
    calc 2 ^ (s * (h - 1)) = (2 ^ s) ^ (h - 1) := pow_mul _ _ _
      _ ≤ q ^ (h - 1) := Nat.pow_le_pow_left hq _
      _ < 8 * 2 ^ N := hmin
      _ = 2 ^ (N + 3) := by ring
  have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 this
  have : s * h = s * (h - 1) + s := by
    have e : h = (h - 1) + 1 := by omega
    calc s * h = s * ((h - 1) + 1) := by rw [← e]
      _ = s * (h - 1) + s := by ring
  omega

theorem finish (p s : ℕ) (hp : 2 ≤ p) (hs : 1 ≤ s) (hq : Fintype.card F = p ^ s) (hsN : s ≤ N)
    (C0 : Submodule F (Fin N → F)) (hC0 : C0 ≠ ⊥) (f g : Fin N → F) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hrel : Γ < relDist C0) (hf : Γ < distToCode f C0) (hg : Γ < distToCode g C0) :
    ∃ C : Submodule F (Fin N → F), C0 ≤ C ∧ C ≠ ⊥ ∧ relDist C = relDist C0 ∧
      |rate C - (1 - relDist C)| ≤ 4 / (s : ℝ) ∧ Γ < distToCode f C ∧ Γ < distToCode g C := by
  classical
  have hN : 0 < N := lt_of_lt_of_le hs hsN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2s : 2 ^ s ≤ Fintype.card F := by
    rw [hq]; exact Nat.pow_le_pow_left hp s
  obtain ⟨h, h1, hh, hsh⟩ := exists_h (Fintype.card F) s N h2s hs
  set b0 : ℕ := ⌊Γ * N⌋₊ with hb0
  have hd0 : (b0 : ℝ) ≤ Γ * N := Nat.floor_le (by positivity)
  have hrel' : Γ * N < (minDist C0 : ℝ) := by
    unfold relDist at hrel
    rw [Fintype.card_fin, lt_div_iff₀ hNr] at hrel
    exact hrel
  have hbd : b0 < minDist C0 := by
    have : (b0 : ℝ) < minDist C0 := lt_of_le_of_lt hd0 hrel'
    exact_mod_cast this
  have hdist : ∀ x : Fin N → F, Γ < distToCode x C0 → ∀ u : Fin N → F, hammingNorm u ≤ b0 →
      x - u ∉ C0 := by
    intro x hx u hu hmem
    have h1 := distToCode_le_of_mem C0 x (x - u) hmem
    have e : hammingDist x (x - u) = hammingNorm u := by rw [← hnorm_eq, sub_sub_cancel]
    rw [e] at h1
    have h2 : (hammingNorm u : ℝ) ≤ Γ * N := le_trans (by exact_mod_cast hu) hd0
    have h3 : (hammingNorm u : ℝ) / N ≤ Γ := by rw [div_le_iff₀ hNr]; exact h2
    linarith
  obtain ⟨C, hC0C, hmd, hsing, hfg⟩ := Enlarge.enlarge C0 hC0 f g b0 hbd (hdist f hf) (hdist g hg) h hh
  have hCbot : C ≠ ⊥ := fun hb => hC0 (le_bot_iff.1 (hb ▸ hC0C))
  refine ⟨C, hC0C, hCbot, ?_, ?_, ?_, ?_⟩
  · unfold relDist; rw [hmd]
  · have hs1 := Enlarge.finrank_le_singleton C hCbot
    rw [hmd] at hs1
    have hrd : relDist C = (minDist C0 : ℝ) / N := by unfold relDist; rw [hmd, Fintype.card_fin]
    have hrt : rate C = (finrank F C : ℝ) / N := by unfold rate; rw [Fintype.card_fin]
    rw [hrd, hrt]
    have hsr : (0 : ℝ) < s := by exact_mod_cast hs
    have hkey : |((finrank F C : ℝ) + minDist C0 - N)| ≤ h := by
      have a1 : ((finrank F C : ℝ) + minDist C0) ≤ N + 1 := by exact_mod_cast hs1
      have a2 : (N : ℝ) + 1 ≤ finrank F C + minDist C0 + h := by exact_mod_cast hsing
      have a3 : (1 : ℝ) ≤ h := by exact_mod_cast h1
      rw [abs_le]; constructor <;> linarith
    have e : (finrank F C : ℝ) / N - (1 - (minDist C0 : ℝ) / N) =
        ((finrank F C : ℝ) + minDist C0 - N) / N := by field_simp; ring
    rw [e, abs_div, abs_of_pos hNr, div_le_div_iff₀ hNr hsr]
    have a4 : (s : ℝ) * h ≤ N + 2 + s := by exact_mod_cast hsh
    have a5 : (s : ℝ) ≤ N := by exact_mod_cast hsN
    have a6 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [mul_le_mul_of_nonneg_right hkey hsr.le]
  · exact distToCode_gt_of C hN f Γ b0 hb0 hΓ (fun u hu => (hfg u hu).1)
  · exact distToCode_gt_of C hN g Γ b0 hb0 hΓ (fun u hu => (hfg u hu).2)

end ProxGapTight.Dev.Main3
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProxGapTight.Dev.Main
open ProxGapTight.Dev.Main1 ProxGapTight.Dev.Main2 ProxGapTight.Dev.Main3

lemma nm_pos (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 1 ≤ m) : 0 < nm Q m := by
  unfold nm
  apply Nat.div_pos _ (by omega)
  have : Q ^ 1 ≤ Q ^ m := Nat.pow_le_pow_right (by omega) hm
  simp at this
  omega

lemma em_le_nm (Q m : ℕ) (hQ : 2 ≤ Q) : em Q m ≤ nm Q m := by
  unfold em nm
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right (by omega) (by omega)

lemma m_le_s (p a m r s : ℕ) (hp : 2 ≤ p) (ha : 1 ≤ a) (hr : r ≤ 2 * a)
    (h : (p ^ a) ^ (2 * m) = (p ^ s) ^ r) : m ≤ s := by
  rw [← pow_mul, ← pow_mul] at h
  have := Nat.pow_right_injective hp h
  by_contra hms
  push_neg at hms
  have h1 : s * r ≤ s * (2 * a) := Nat.mul_le_mul_left _ hr
  have h2 : a * (2 * m) = s * r := this
  have : 2 * a * s < 2 * a * m := Nat.mul_lt_mul_of_pos_left hms (by omega)
  nlinarith

end ProxGapTight.Dev.Main

namespace ProxGapTight
open ProxGapTight.Dev.Main ProxGapTight.Dev.Main1 ProxGapTight.Dev.Main2 ProxGapTight.Dev.Main3

theorem chk_theorem_1_1_johnson_tight :
    ∀ p : ℕ, p.Prime → ∀ δ ρ η : ℝ, 0 < δ → δ < 1 → J32 δ < ρ → ρ < Gam δ → 0 < η →
      ∃ A c K : ℝ, 0 < A ∧ 0 < c ∧ ∃ D s₀ : ℕ, 1 ≤ D ∧ 1 ≤ s₀ ∧
        ∀ s : ℕ, s₀ ≤ s → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = p ^ s →
          ∀ N : ℕ, A * (s : ℝ) ^ D ≤ (N : ℝ) → N < p ^ s →
            ∃ C : Submodule F (Fin N → F), ∃ f g : Fin N → F,
              C ≠ ⊥ ∧ |relDist C - δ| < η ∧ |rate C - (1 - relDist C)| ≤ K / (s : ℝ) ∧
              Gam δ < distToCode f C ∧ Gam δ < distToCode g C ∧
              c * ((p : ℝ) ^ s) ≤ ((exceptionalSet ρ f g C).card : ℝ) := by
  intro p hp δ ρ η hδ0 hδ1 hJ hρ hη
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨hord1, hord2⟩ := thresholds_ordered δ hδ0 hδ1
  have hΓ0 : 0 ≤ Gam δ := by
    unfold Gam
    have : (1 - δ) ^ ((4 : ℝ) / 9) < 1 :=
      Real.rpow_lt_one (by linarith) (by linarith) (by norm_num)
    linarith
  set Γ := Gam δ with hΓ
  set η0 : ℝ := min η ((δ - Γ) / 4) with hη0
  have hη0pos : 0 < η0 := lt_min hη (by linarith)
  have hη0η : η0 ≤ η := min_le_left _ _
  have hη0δ : η0 ≤ (δ - Γ) / 4 := min_le_right _ _
  obtain ⟨Q₀, hQ₀⟩ := parameter_choice δ ρ η hδ0 hδ1 hJ hρ hη
  set a : ℕ := max Q₀ 121 + 1 with ha
  have ha1 : 1 ≤ a := by omega
  have hQa : a < p ^ a := Nat.lt_pow_self (by omega)
  have hQ : 32 < p ^ a := by omega
  have h49 : p ^ a ≠ 49 := by omega
  have h121 : p ^ a ≠ 121 := by omega
  obtain ⟨t, ht, ξ0, hξ0, m₀, hm₀⟩ := hQ₀ (p ^ a) (by omega)
  set ξ : ℝ := min ξ0 (η0 / 8) with hξdef
  have hξ : 0 < ξ := lt_min hξ0 (by linarith)
  have hξξ0 : ξ ≤ ξ0 := min_le_left _ _
  have hξη : ξ ≤ η0 / 8 := min_le_right _ _
  obtain ⟨c, hc, s₁, hbase⟩ := base_data_proof p a hQ h49 h121 (max m₀ 4)
  obtain ⟨A, hA, harith⟩ := arith p a hp2 ξ hξ
  refine ⟨max A 1, c, 4, lt_of_lt_of_le one_pos (le_max_right _ _), hc, 2 * a * (p - 1) + 1,
    max (max s₁ 1) (⌈1 / ξ⌉₊ + 1), by omega, by omega, ?_⟩
  intro s hs F iF iFin iDec hF N hN hNq
  have hs1 : s₁ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs2 : 1 ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hs3 : ⌈1 / ξ⌉₊ + 1 ≤ s := le_trans (le_max_right _ _) hs
  obtain ⟨E, iE, iEF, iED, iEA, m, r, Cm, D, fm, gm, T, hm1, hr1, hr2, hE, hmr, hCm, hCD, hfD, hgD,
    hDcard, hL1, hL2, hdf, hdg, hTc, hT⟩ := hbase s hs1 F hF
  have hms : m ≤ s := m_le_s p a m r s hp2 ha1 hr2 hmr
  have hm4 : 4 ≤ m := le_trans (le_max_right _ _) hm1
  have hmm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hm1
  have hn : 0 < nm (p ^ a) m := nm_pos _ _ (by omega) (by omega)
  have hen : em (p ^ a) m ≤ nm (p ^ a) m := em_le_nm _ _ (by omega)
  obtain ⟨H1, H2, H3⟩ := hm₀ m hmm₀
  have hqξ : 1 / (Fintype.card F : ℝ) < ξ := by
    have h1 : (s : ℝ) < (Fintype.card F : ℝ) := by
      rw [hF]; exact_mod_cast Nat.lt_pow_self (by omega : 1 < p)
    have h2 : 1 / ξ < (s : ℝ) := by
      have := Nat.le_ceil (1 / ξ)
      have h3 : ((⌈1 / ξ⌉₊ + 1 : ℕ) : ℝ) ≤ s := by exact_mod_cast hs3
      push_cast at h3
      linarith
    have h4 : 1 / ξ < (Fintype.card F : ℝ) := by linarith
    rw [div_lt_iff₀ (by positivity)] at h4 ⊢
    nlinarith
  have hNA : A * (s : ℝ) ^ (2 * a * (p - 1) + 1) ≤ (N : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hN
  have hsN : s ≤ N := by
    have h1 : (s : ℝ) ≤ (s : ℝ) ^ (2 * a * (p - 1) + 1) := by
      calc (s : ℝ) = (s : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast hs2) (by omega)
    have h2 : (1 : ℝ) * (s : ℝ) ^ (2 * a * (p - 1) + 1) ≤ (max A 1) * (s : ℝ) ^ (2 * a * (p - 1) + 1) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    exact_mod_cast (by linarith : (s : ℝ) ≤ N)
  have hN1 : 1 ≤ N := le_trans hs2 hsN
  -- union bound
  have hU := harith s m r hs2 hms hr2 N hNA
  have hDr : (Nat.card D : ℝ) * (2 * Real.exp (-2 * ξ ^ 2 * (N : ℝ))) < 1 := by
    refine lt_of_le_of_lt ?_ hU
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hDcard) (by positivity)
  obtain ⟨ω, hω⟩ := exists_good (F := F) (E := E) (nm (p ^ a) m) t N hn ht hN1 ξ hξ D hDr
  have hξ3 : ∀ x, x + 3 * ξ0 < ρ → x + 3 * ξ < ρ := fun x hx => by linarith
  obtain ⟨hbot, hrel, hfd, hgd, hex⟩ := analysis (F := F) (E := E) (n := nm (p ^ a) m) (t := t)
    (N := N) hn hN1 ω ξ δ Γ ρ η0 (Lm (p ^ a) m) (em (p ^ a) m) hen hξ hξη
    (by linarith) hη0pos hqξ Cm D fm gm T hCD hfD hgD hCm hω (by linarith) (by linarith)
    H3 hL1 hL2 hdf hdg hT
  have hrelΓ : Γ < relDist (Cm.map (ampLin ω)) := by
    rw [abs_lt] at hrel; linarith [hrel.1]
  obtain ⟨C, hC0C, hCbot, hrelC, hrate, hfC, hgC⟩ := finish (F := F) p s hp2 hs2 hF hsN
    (Cm.map (ampLin ω)) hbot (amp ω fm) (amp ω gm) Γ hΓ0 hrelΓ hfd hgd
  refine ⟨C, amp ω fm, amp ω gm, hCbot, ?_, hrate, hfC, hgC, ?_⟩
  · rw [hrelC]; exact lt_of_lt_of_le hrel hη0η
  · have hsub : T ⊆ exceptionalSet ρ (amp ω fm) (amp ω gm) C := by
      intro z hz
      unfold exceptionalSet
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_trans (distToCode_mono _ C hC0C _) (hex z hz)
    have := Finset.card_le_card hsub
    have h2 : (T.card : ℝ) ≤ ((exceptionalSet ρ (amp ω fm) (amp ω gm) C).card : ℝ) := by
      exact_mod_cast this
    push_cast at hTc
    linarith

end ProxGapTight
end

theorem solution : type_of% @ProxGapTight.chk_theorem_1_1_johnson_tight := @ProxGapTight.chk_theorem_1_1_johnson_tight
