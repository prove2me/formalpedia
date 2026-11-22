-- Prove2me | solution 1 for ZhangYeung.theorem5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:13:13.219339+00:00
-- url     : https://prove2.me/submissions/f8364aa7-807b-4f0d-8e91-757b6d0ef238

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem5
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_mutualInfo_eq
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_IsUniform_comp
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_congr
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_mutualInfo_def
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteRight_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
public import Theorems.Thm_ProbabilityTheory_condIndep_copies
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_comm
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq_zero
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_nonneg
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_ProbabilityTheory_mutualInfo_comm
public import Theorems.Thm_ProbabilityTheory_mutualInfo_const
public import Theorems.Thm_ZhangYeung_IdentDistrib_condMutualInfo_eq
public import Theorems.Thm_ZhangYeung_condIndepFun_comp
public import Theorems.Thm_ZhangYeung_delta_def
public import Theorems.Thm_ZhangYeung_delta_of_condMI_vanishes_eq
public import Theorems.Thm_ZhangYeung_mutualInfo_add_three_way_identity
public import Theorems.Thm_ZhangYeung_mutualInfo_le_of_condIndepFun
public import Theorems.Thm_prod_eq
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
attribute [local simp] ProbabilityTheory.Kernel.entropy_compProd_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_const
attribute [local simp] ProbabilityTheory.Kernel.entropy_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_prod
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkLeft
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkRight
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_kernel
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_measure
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteRight_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_snd_reverse
attribute [local simp] ProbabilityTheory.identDistrib_id
attribute [local simp] ProbabilityTheory.indepFun_zero_measure
attribute [local simp] prod_eq


section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
section Helpers
variable {Ω : Type*} [MeasurableSpace Ω]
private lemma mutualInfo_comp_right_of_injective
    {α β γ : Type*}
    [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β}
    (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω)
    {f : β → γ} (hf : Function.Injective f) :
    I[X : f ∘ Y; μ] = I[X : Y; μ] := by
  have h_joint : H[⟨X, f ∘ Y⟩; μ] = H[⟨X, Y⟩; μ] := by
    let g : α × β → α × γ := fun p => (p.1, f p.2)
    have hg : Function.Injective g := by
      intro p q hpq
      rcases p with ⟨xp, yp⟩
      rcases q with ⟨xq, yq⟩
      simp only [g, Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 (hf hpq.2)
    change H[g ∘ ⟨X, Y⟩; μ] = H[⟨X, Y⟩; μ]
    exact entropy_comp_of_injective μ (hX.prodMk hY) g hg
  rw [mutualInfo_def, mutualInfo_def, entropy_comp_of_injective μ hY f hf, h_joint]
private lemma mutualInfo_pair_swap_right
    {α β γ : Type*}
    [Finite α] [Finite β] [Finite γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) :
    I[X : ⟨Y, Z⟩; μ] = I[X : ⟨Z, Y⟩; μ] := by
  change I[X : fun a => (Y a, Z a); μ] =
    I[X : Prod.swap ∘ (fun a => (Y a, Z a)); μ]
  exact (mutualInfo_comp_right_of_injective hX (hY.prodMk hZ) μ
    (f := Prod.swap) Prod.swap_injective).symm
private lemma measurable_pairZU
    {n : ℕ} {S : Fin n → Type*} {S_Z S_U : Type*}
    [∀ i, MeasurableSpace (S i)] [MeasurableSpace S_Z] [MeasurableSpace S_U] :
    Measurable (fun p : (∀ i : Fin n, S i) × (S_Z × S_U) => p.2) := by
  fun_prop
private lemma measurable_pairXZU
    {n : ℕ} {S : Fin n → Type*} {S_Z S_U : Type*}
    [∀ i, MeasurableSpace (S i)] [MeasurableSpace S_Z] [MeasurableSpace S_U]
    (i : Fin n) :
    Measurable (fun p : (∀ j : Fin n, S j) × (S_Z × S_U) => (p.1 i, p.2)) := by
  fun_prop
private lemma measurable_projZUX
    {n : ℕ} {S : Fin n → Type*} {S_Z S_U : Type*}
    [∀ i, MeasurableSpace (S i)] [MeasurableSpace S_Z] [MeasurableSpace S_U]
    (i : Fin n) :
    Measurable (fun p : (∀ j : Fin n, S j) × (S_Z × S_U) => (p.2.1, p.2.2, p.1 i)) := by
  fun_prop
private lemma tuple_condIndepFun_pairProj
    {n : ℕ} {S : Fin n → Type*} {T : Type*}
    [∀ i, MeasurableSpace (S i)] [MeasurableSpace T]
    {μ : Measure Ω} {Xprime Xstar : Ω → ∀ i : Fin n, S i} {V : Ω → T}
    (i k : Fin n) (h : CondIndepFun Xprime Xstar V μ) :
    CondIndepFun (fun ω => Xprime ω i) (fun ω => Xstar ω k) V μ := by
  exact ZhangYeung.condIndepFun_comp (φ := fun x => x i) (ψ := fun x => x k)
    (measurable_pi_apply i) (measurable_pi_apply k) h
private lemma mutualInfo_add_n_way_inequality
    {n : ℕ} {α : Type*} {β : Fin n → Type*}
    [Finite α] [∀ k, Finite (β k)]
    [MeasurableSpace α] [∀ k, MeasurableSpace (β k)]
    [MeasurableSingletonClass α] [∀ k, MeasurableSingletonClass (β k)]
    {A : Ω → α} {B : ∀ k : Fin n, Ω → β k}
    (hA : Measurable A) (hB : ∀ k, Measurable (B k))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∑ k, I[A : B k; μ]
      ≤ I[A : (fun ω => fun k : Fin n => B k ω); μ]
        + ∑ k, H[B k; μ]
        - H[(fun ω => fun k : Fin n => B k ω); μ] := by
  induction n with
  | zero =>
      let c : ∀ k : Fin 0, β k := fun k => nomatch k
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      have htuple : (fun ω => fun k : Fin 0 => B k ω) = fun _ : Ω => c := by
        funext ω k
        exact Fin.elim0 k
      rw [htuple]
      have hconstMI : I[A : (fun _ : Ω => c); μ] = 0 := mutualInfo_const hA c
      have hconstH : H[(fun _ : Ω => c); μ] = 0 := by
        simp
      linarith
  | succ n ih =>
      let Binit : ∀ k : Fin n, Ω → β k.castSucc := fun k => B k.castSucc
      let Blast : Ω → β (Fin.last n) := B (Fin.last n)
      let BinitTuple : Ω → (∀ k : Fin n, β k.castSucc) := fun ω k => B k.castSucc ω
      let Btuple : Ω → (∀ k : Fin (n + 1), β k) := fun ω k => B k ω
      have hBinit : ∀ k : Fin n, Measurable (Binit k) := fun k => hB k.castSucc
      have hBlast : Measurable Blast := hB (Fin.last n)
      have hBinitTuple : Measurable BinitTuple := measurable_pi_lambda _ hBinit
      have hBtuple : Measurable Btuple := measurable_pi_lambda _ hB
      have h_tail := ih (β := fun k => β k.castSucc) (B := Binit) hBinit
      let pack : (∀ k : Fin (n + 1), β k) → (∀ k : Fin n,
        β k.castSucc) × β (Fin.last n) :=
        fun x => (fun k => x k.castSucc, x (Fin.last n))
      have hpack : Function.Injective pack := by
        intro x y hxy
        have hxyInit : (fun k : Fin n => x (Fin.castSucc k)) =
          fun k : Fin n => y (Fin.castSucc k) :=
          (Prod.mk.inj hxy).1
        have hxyLast : x (Fin.last n) = y (Fin.last n) := (Prod.mk.inj hxy).2
        ext i
        rcases Fin.eq_castSucc_or_eq_last i with hi | rfl
        · obtain ⟨j, rfl⟩ := hi
          exact congrFun hxyInit j
        · exact hxyLast
      have h_tuple_ent : H[⟨BinitTuple, Blast⟩; μ] = H[Btuple; μ] := by
        change H[pack ∘ Btuple; μ] = H[Btuple; μ]
        exact entropy_comp_of_injective μ hBtuple pack hpack
      have h_tuple_mi : I[A : ⟨BinitTuple, Blast⟩; μ] = I[A : Btuple; μ] := by
        have h_joint : H[⟨A, ⟨BinitTuple, Blast⟩⟩; μ] = H[⟨A, Btuple⟩; μ] := by
          let packA : α × (∀ k : Fin (n + 1), β k) → α × ((∀ k : Fin n,
            β k.castSucc) × β (Fin.last n)) :=
            fun p => (p.1, pack p.2)
          have hpackA : Function.Injective packA := by
            intro p q hpq
            rcases p with ⟨a₁, x⟩
            rcases q with ⟨a₂, y⟩
            have hpq' : (a₁, pack x) = (a₂, pack y) := by simpa [packA] using hpq
            exact Prod.ext (Prod.mk.inj hpq').1 (hpack (Prod.mk.inj hpq').2)
          change H[packA ∘ ⟨A, Btuple⟩; μ] = H[⟨A, Btuple⟩; μ]
          exact entropy_comp_of_injective μ (hA.prodMk hBtuple) packA hpackA
        rw [mutualInfo_def, mutualInfo_def, h_tuple_ent, h_joint]
      have h_three :
          I[A : BinitTuple; μ] + I[A : Blast; μ]
            = I[A : ⟨BinitTuple, Blast⟩; μ] + I[BinitTuple : Blast; μ]
              - I[BinitTuple : Blast | A; μ] := by
        simpa using (mutualInfo_add_three_way_identity (X := A) (Y := BinitTuple) (Z :=
          Blast) hA hBinitTuple hBlast μ)
      have h_nonneg : 0 ≤ I[BinitTuple : Blast | A; μ] :=
        condMutualInfo_nonneg hBinitTuple hBlast
      have h_pairInfo : I[BinitTuple : Blast; μ] =
        H[BinitTuple; μ] + H[Blast; μ] - H[Btuple; μ] := by
        rw [mutualInfo_def, h_tuple_ent]
      have h_split :
          I[A : BinitTuple; μ] + I[A : Blast; μ]
            ≤ I[A : Btuple; μ] + H[BinitTuple; μ] + H[Blast; μ] - H[Btuple; μ] := by
        rw [h_tuple_mi, h_pairInfo] at h_three
        linarith
      have h_sum_tail :
          ∑ k : Fin (n + 1), I[A : B k; μ]
            = (∑ k : Fin n, I[A : B k.castSucc; μ]) + I[A : Blast; μ] := by
        simpa [Blast] using (Fin.sum_univ_castSucc (f := fun k : Fin (n + 1) => I[A : B k; μ]))
      have h_sum_entropy :
          ∑ k : Fin (n + 1), H[B k; μ]
            = (∑ k : Fin n, H[B k.castSucc; μ]) + H[Blast; μ] := by
        simpa [Blast] using (Fin.sum_univ_castSucc (f := fun k : Fin (n + 1) => H[B k; μ]))
      rw [h_sum_tail, h_sum_entropy]
      linarith
end Helpers
section MainTheorems
variable {Ω : Type*} [MeasurableSpace Ω]
  {n : ℕ}
  {S_U S_Z : Type u} {S : Fin n → Type u}
  [MeasurableSpace S_U] [MeasurableSpace S_Z]
  [∀ i, MeasurableSpace (S i)]
  [Finite S_U] [Finite S_Z] [∀ i, Finite (S i)]
  [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
  [∀ i, MeasurableSingletonClass (S i)]
end MainTheorems
end ZhangYeung
end
end

set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
variable {Ω : Type*} [MeasurableSpace Ω]
  {n : ℕ}
  {S_U S_Z : Type u} {S : Fin n → Type u}
  [MeasurableSpace S_U] [MeasurableSpace S_Z]
  [∀ i, MeasurableSpace (S i)]
  [Finite S_U] [Finite S_Z] [∀ i, Finite (S i)]
  [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
  [∀ i, MeasurableSingletonClass (S i)]
namespace ZhangYeung
namespace _root_.ZhangYeung
theorem _root_.solution
    {U : Ω → S_U} {Z : Ω → S_Z} {X : ∀ i : Fin n, Ω → S i}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : Fin n) :
    2 ≤ n →
    n * I[U : Z; μ] - ∑ j, I[U : Z | X j; μ] - n * I[U : Z | X i; μ]
      ≤ I[X i : ⟨U, Z⟩; μ]
        + ∑ j, H[X j; μ]
        - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] := by
  intro _hn
  let Xtuple : Ω → (∀ j : Fin n, S j) := fun ω j => X j ω
  let ZU : Ω → S_Z × S_U := fun ω => (Z ω, U ω)
  have hXtuple : Measurable Xtuple := measurable_pi_lambda _ hX
  have hZU : Measurable ZU := hZ.prodMk hU
  obtain ⟨Ω', mΩ', Xprime, Xstar, V, ν, hν, hXprime, hXstar, hV, hCond, hFirst, hSecond⟩ :=
    condIndep_copies Xtuple ZU hXtuple hZU μ
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure ν := hν
  let Z' : Ω' → S_Z := fun ω => (V ω).1
  let U' : Ω' → S_U := fun ω => (V ω).2
  let X' : ∀ j : Fin n, Ω' → S j := fun j ω => Xprime ω j
  let XstarCoord : ∀ j : Fin n, Ω' → S j := fun j ω => Xstar ω j
  have hZ' : Measurable Z' := measurable_fst.comp hV
  have hU' : Measurable U' := measurable_snd.comp hV
  have hX' : ∀ j, Measurable (X' j) := fun j => (measurable_pi_apply j).comp hXprime
  have hXstarCoord : ∀ j,
    Measurable (XstarCoord j) := fun j => (measurable_pi_apply j).comp hXstar
  have hPair : ∀ k : Fin n,
    delta Z' U' (X' i) (XstarCoord k) ν ≤ I[X' i : XstarCoord k; ν] := by
    intro k
    have hVanish : I[X' i : XstarCoord k | (fun ω' => (Z' ω', U' ω')); ν] = 0 := by
      simpa [Z', U'] using (condMutualInfo_eq_zero (hX' i) (hXstarCoord k)).mpr
        (tuple_condIndepFun_pairProj i k hCond)
    rw [delta_of_condMI_vanishes_eq (hX' i) hZ' hU' (hXstarCoord k) ν hVanish]
    have h1 : 0 ≤ I[X' i : XstarCoord k | Z'; ν] := condMutualInfo_nonneg (hX' i) (hXstarCoord k)
    have h2 : 0 ≤ I[X' i : XstarCoord k | U'; ν] := condMutualInfo_nonneg (hX' i) (hXstarCoord k)
    have h3 : 0 ≤ I[Z' : U' | ⟨X' i, XstarCoord k⟩; ν] := condMutualInfo_nonneg hZ' hU'
    linarith
  have hTransport : ∀ k : Fin n,
    delta Z U (X i) (X k) μ = delta Z' U' (X' i) (XstarCoord k) ν := by
    intro k
    have hPairZU : IdentDistrib (fun ω => (Z ω, U ω)) (fun ω' => (Z' ω', U' ω')) μ ν :=
      hFirst.symm.comp measurable_pairZU
    have hTripleFirst :
        IdentDistrib (fun ω => (Z ω, U ω, X i ω)) (fun ω' => (Z' ω', U' ω',
          X' i ω')) μ ν :=
      hFirst.symm.comp (measurable_projZUX i)
    have hTripleSecond :
        IdentDistrib (fun ω => (Z ω, U ω, X k ω)) (fun ω' => (Z' ω', U' ω',
          XstarCoord k ω')) μ ν :=
      hSecond.symm.comp (measurable_projZUX k)
    rw [delta_def, delta_def, hPairZU.mutualInfo_eq,
      IdentDistrib.condMutualInfo_eq hZ hU (hX i) hZ' hU' (hX' i) hTripleFirst,
      IdentDistrib.condMutualInfo_eq hZ hU (hX k) hZ' hU' (hXstarCoord k) hTripleSecond]
  have hDeltaSum :
      ∑ k : Fin n, delta Z U (X i) (X k) μ
        = n * I[Z : U; μ] - n * I[Z : U | X i; μ] - ∑ k : Fin n, I[Z : U | X k; μ] := by
    simp_rw [delta_def]
    simp_all
  have hSum :
      n * I[Z : U; μ] - n * I[Z : U | X i; μ] - ∑ k : Fin n, I[Z : U | X k; μ]
        ≤ ∑ k : Fin n, I[X' i : XstarCoord k; ν] := by
    calc
      n * I[Z : U; μ] - n * I[Z : U | X i; μ] - ∑ k : Fin n, I[Z : U | X k; μ]
        = ∑ k : Fin n, delta Z U (X i) (X k) μ := hDeltaSum.symm
      _ = ∑ k : Fin n, delta Z' U' (X' i) (XstarCoord k) ν := by
        simp_all
      _ ≤ ∑ k : Fin n, I[X' i : XstarCoord k; ν] := Finset.sum_le_sum fun k _ => hPair k
  have hChain := mutualInfo_add_n_way_inequality (A := X' i) (B :=
    XstarCoord) (hX' i) hXstarCoord ν
  have hCondProj :
      CondIndepFun (X' i) (fun ω' => fun k : Fin n => XstarCoord k ω') (fun ω' => (Z' ω',
        U' ω')) ν := by
    change CondIndepFun ((fun x => x i) ∘ Xprime) Xstar V ν
    exact (ZhangYeung.condIndepFun_comp (φ := fun x => x i) (ψ := id)
      (measurable_pi_apply i) measurable_id hCond)
  have hDP :
      I[X' i : (fun ω' => fun k : Fin n => XstarCoord k ω'); ν]
        ≤ I[X' i : (fun ω' => (Z' ω', U' ω')); ν] :=
    mutualInfo_le_of_condIndepFun (hX' i) hXstar (hZ'.prodMk hU') ν hCondProj
  have hMargXZU :
      I[X' i : (fun ω' => (Z' ω', U' ω')); ν]
        = I[X i : (fun ω => (Z ω, U ω)); μ] := by
    have hPairXZU :
        IdentDistrib (fun ω => (X i ω, (Z ω, U ω)))
          (fun ω' => (X' i ω', (Z' ω', U' ω'))) μ ν :=
      hFirst.symm.comp (measurable_pairXZU i)
    exact hPairXZU.mutualInfo_eq.symm
  have hTupleSecond :
      IdentDistrib (fun ω' => fun k : Fin n => XstarCoord k ω') (fun ω => fun k :
        Fin n => X k ω) ν μ :=
    hSecond.comp measurable_fst
  have hMargJoint :
      H[(fun ω' => fun k : Fin n => XstarCoord k ω'); ν] =
        H[(fun ω : Ω => fun k : Fin n => X k ω); μ] :=
    hTupleSecond.entropy_congr
  have hMargSingle : ∀ k : Fin n, H[XstarCoord k; ν] = H[X k; μ] := by
    intro k
    have hCoord : IdentDistrib (XstarCoord k) (X k) ν μ :=
      hTupleSecond.comp (measurable_pi_apply k)
    exact hCoord.entropy_congr
  have hMargSingles : ∑ k : Fin n, H[XstarCoord k; ν] = ∑ k : Fin n, H[X k; μ] := by
    simp_all
  have hInternal :
      n * I[Z : U; μ] - ∑ j, I[Z : U | X j; μ] - n * I[Z : U | X i; μ]
        ≤ I[X i : (fun ω => (Z ω, U ω)); μ]
          + ∑ j, H[X j; μ]
          - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] := by
    linarith [hSum, hChain, hDP, hMargXZU, hMargJoint, hMargSingles]
  have hCondComm : (fun j : Fin n => I[Z : U | X j; μ]) = fun j : Fin n => I[U : Z | X j; μ] := by
    funext j
    exact condMutualInfo_comm hZ hU (X j) μ
  have hSwapRhs :
      I[X i : (fun ω => (Z ω, U ω)); μ] = I[X i : ⟨U, Z⟩; μ] := by
    simpa using mutualInfo_pair_swap_right (hX i) hZ hU μ
  have hPaperOrder :
      n * I[U : Z; μ] - ∑ j, I[U : Z | X j; μ] - n * I[U : Z | X i; μ]
        ≤ I[X i : (fun ω => (Z ω, U ω)); μ]
          + ∑ j, H[X j; μ]
          - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] := by
    have hCondI : I[Z : U | X i; μ] = I[U : Z | X i; μ] := condMutualInfo_comm hZ hU (X i) μ
    simpa [hCondComm, hCondI, mutualInfo_comm hZ hU μ] using hInternal
  simpa [hSwapRhs] using hPaperOrder
end _root_.ZhangYeung
end ZhangYeung
